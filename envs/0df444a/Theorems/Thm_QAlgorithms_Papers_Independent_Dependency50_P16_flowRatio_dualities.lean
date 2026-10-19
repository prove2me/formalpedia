-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_flowRatio_dualities
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.flowRatio_dualities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:27:27.632979+00:00
-- url     : https://prove2.me/theorems/f8d56e0c-eb36-4c62-a92b-cca40774030b
-- title:
--   Lemma 4.16: Flow-ratio dualities
-- statement:
--   For any finite jump representation on $\mathbb C^n$ and $1\le d<n$, let $R_d$ be its flow ratios and $R'_d$ those obtained by replacing each jump by its adjoint. Then
--
--   $$\sup_U R_{n-d}(U)=\left(\inf_U R_d(U)\right)^{-1},\qquad\sup_U R'_d(U)=\left(\inf_U R_d(U)\right)^{-1}.$$
--
--   The extrema range over $SU(n)$ and exclude only $0/0$. They are taken in $[0,\infty]$, with $0^{-1}=\infty$, $\infty^{-1}=0$, $\sup\varnothing=0$, and $\inf\varnothing=\infty$. This includes scalar-noise and purely Hamiltonian generators.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 20, Lemma 4.16: Flow-ratio dualities

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

/-- arXiv:2308.00561v1, PDF p.20, Lemma 4.16: Flow-ratio dualities. Convention completion: ENNReal complete-lattice extrema. At an empty ratio domain both suprema are 0 and inverse infimum is infinity inverse = 0. Right multiplication by basis permutations is the adapted-basis convention. -/
theorem flowRatio_dualities {n r : ℕ} (hn : 2 ≤ n) (V : Fin r → Mat n)
    (d : ℕ) (hd : 1 ≤ d) (hdn : d < n) :
    flowSup V (n - d) = (flowInf V d)⁻¹ ∧
      flowSup (fun k => (V k)ᴴ) d = (flowInf V d)⁻¹ := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
