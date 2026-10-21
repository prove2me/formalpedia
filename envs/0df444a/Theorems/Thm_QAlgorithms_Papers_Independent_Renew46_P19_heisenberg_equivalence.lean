-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P19_heisenberg_equivalence
-- name    : QAlgorithms.Papers.Independent.Renew46.P19.heisenberg_equivalence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:24:00.481826+00:00
-- url     : https://prove2.me/theorems/7599cce4-40fb-48fa-9a3f-c56e6b370cfe
-- title:
--   Unitary equivalence and irreducibility on the window range
-- statement:
--   Let $n\ge1$, $\hbar>0$, and let $\phi\in\mathcal S(\mathbb R^n)$ have norm one. Write $\mathcal H_\phi=\operatorname{ran}W_\phi$ and $\widehat T(x_0,p_0)\psi(x)=e^{i(p_0\cdot x-p_0\cdot x_0/2)/\hbar}\psi(x-x_0)$. The map $W_\phi$ is a unitary map onto $\mathcal H_\phi$ satisfying
--
--   $$
--   \widetilde T(d)W_\phi=W_\phi\widehat T(d).
--   $$
--
--   The phase operators are unitary and the operators $e^{it/\hbar}\widetilde T(d)$ form a strongly continuous representation with multiplication $(d,t)(e,s)=(d+e,t+s+\sigma(d,e)/2)$. On $\mathcal H_\phi$ this representation is irreducible: its only closed invariant complex linear subspaces are $\{0\}$ and $\mathcal H_\phi$.
--
--   The restriction to a single window range is essential to this representation result.
-- source:
--   A new approach to the star-genvalue equation, arXiv:0808.0489v1, PDF p. 6, §3, paragraph before Proposition 2

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P19

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Renew46.P19

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates Quadrature)

open QAlgorithms.Papers.Independent.Next46.P20
  (ConfigurationL2 PhaseL2 phasePosition phaseMomentum phasePoint)

open QAlgorithms.Papers.Independent.Claimed50.P05 (spectrumOf pointSpectrum)

open QAlgorithms.Papers.Independent.Frontier30.P10 (symplecticPair)

local notation "sigma" => fun {n : ℕ} (z w : PhaseCoordinates n) =>
  symplecticPair (Sum.elim (phasePosition z) (phaseMomentum z))
    (Sum.elim (phasePosition w) (phaseMomentum w))

/-- PDF pp.5–6: unitary equivalence and irreducibility on H_phi only.
The central multiplication is (d,t)(e,s)=(d+e,t+s+sigma(d,e)/2). -/
theorem heisenberg_equivalence {n : ℕ} (hn : 0 < n) (hbar : ℝ) (hhbar : 0 < hbar)
    (phi : SchwartzMap (Configuration n) ℂ)
    (hphi : ‖phi.toLp 2 (volume : Measure (Configuration n))‖ = 1) :
    let phiL2 := phi.toLp 2 (volume : Measure (Configuration n))
    (∀ d : PhaseCoordinates n, RealizesPhaseShift hbar d (phaseOperator hbar d) ∧
      RealizesConfigurationShift hbar d (configurationOperator hbar d) ∧
      Isometry (phaseOperator hbar d) ∧ Function.Surjective (phaseOperator hbar d)) ∧
    (∀ (d e : PhaseCoordinates n) (t s : ℝ),
      (heisenbergOperator hbar d t).comp (heisenbergOperator hbar e s) =
      heisenbergOperator hbar (d + e) (t + s + sigma d e / 2)) ∧
    (∀ f : PhaseL2 n, Continuous (fun q : PhaseCoordinates n × ℝ =>
      heisenbergOperator hbar q.1 q.2 f)) ∧
    (∃ E : ConfigurationL2 n ≃ₗᵢ[ℂ] windowRange hbar phiL2,
      (∀ psi, (E psi : PhaseL2 n) = windowMap hbar phiL2 psi) ∧
      ∀ d psi, phaseOperator hbar d (E psi : PhaseL2 n) =
        (E (configurationOperator hbar d psi) : PhaseL2 n)) ∧
    (∀ K : Submodule ℂ (PhaseL2 n), IsClosed (K : Set (PhaseL2 n)) →
      K ≤ windowRange hbar phiL2 →
      (∀ d f, f ∈ K → phaseOperator hbar d f ∈ K) →
        K = ⊥ ∨ K = windowRange hbar phiL2) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P19

end
