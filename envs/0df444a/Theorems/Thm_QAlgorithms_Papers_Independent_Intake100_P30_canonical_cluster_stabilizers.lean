-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_canonical_cluster_stabilizers
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.canonical_cluster_stabilizers
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:55:48.079407+00:00
-- url     : https://prove2.me/theorems/835a5b80-47af-49c5-a10b-b85e8b3aa65c
-- title:
--   Appendix C: finite-squeezing canonical cluster stabilizers
-- statement:
--   Let $A$ be a finite real symmetric hollow zero-one adjacency matrix, let $r_j>0$, and put $\epsilon_j=e^{-2r_j}$ and $Z=A+i\operatorname{diag}(\epsilon_j)$. The normalized Gaussian wavefunction $\psi_Z$ has nullifiers $p_j-\sum_k Z_{jk}q_k$ and is fixed by
--
--   $$S_j(s)=e^{-\epsilon_js^2/2}X_j(s)Z_j(i\epsilon_js)\prod_l Z_l(A_{jl}s),\qquad s\in\mathbb R,$$
--
--   where $X_j(s)$ translates $q_j$ to $q_j-s$ and $Z_j(t)$ multiplies by $e^{itq_j}$. These concrete function actions uniquely determine its normalized $L^2$ ray. The Gaussian scalar is retained. As common squeezing tends to infinity, the actions on test functions tend to the formal ideal stabilizer actions; no normalized ideal vector is asserted.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 22, Appendix C: finite-squeezing canonical cluster stabilizers

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF pp.22–23, (C7)–(C10): finite stabilizers uniquely determine
the canonical approximate cluster state, up to phase. Equality for arbitrary
L2 representatives is almost everywhere. The ideal limit is an action limit
on test functions, never a limiting normalized eigenket. -/
theorem canonical_cluster_stabilizers (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hHollow : ∀ j, A j j = 0)
    (hWeights : ∀ j k, A j k = 0 ∨ A j k = 1)
    (r : Fin n → ℝ) (hr : ∀ j, 0 < r j) :
    let eps := fun j => Real.exp (-2*r j)
    let Z := complexify A + Complex.I • complexify (Matrix.diagonal eps)
    let f := gaussianWave (Matrix.diagonal eps) (-A)
    NormalizedGaussian f ∧ extractedGraph f = Z ∧
    (∀ j s q, clusterStabilizer A eps j s f q = f q) ∧
    (∀ j q, nullifier Z f j q = 0) ∧
    (∀ g : (Fin n → ℝ) → ℂ, NormalizedWave g →
      (∀ j s, clusterStabilizer A eps j s g =ᵐ[volume] g) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ g =ᵐ[volume] (fun q => c * f q)) ∧
    (∀ (g : (Fin n → ℝ) → ℂ) j s q,
      Tendsto (fun R : ℝ => clusterStabilizer A (fun _ => Real.exp (-2*R)) j s g q) atTop
        (nhds (Complex.exp (Complex.I * ((s * ∑ l, A j l * q l : ℝ) : ℂ)) *
          g (Function.update q j (q j-s))))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
