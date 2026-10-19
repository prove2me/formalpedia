-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P07_singleNegativeVector_rigidity
-- name    : QAlgorithms.Papers.Independent.Information100.P07.singleNegativeVector_rigidity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:33:43.690377+00:00
-- url     : https://prove2.me/theorems/0fd6f212-bcfb-4b48-89dc-eb1cc41b6613
-- title:
--   Lemma E2: one negative Schmidt-rank-two vector forces global channel rigidity
-- statement:
--   Let $\delta$ be a normalized two-qutrit state with completely entangled range and local ranks $(3,3)$. Suppose $\nu>0$, $\|v\|=1$, $v$ has Schmidt rank two, and
--   $$\delta^\Gamma=(\delta^\Gamma)_+-\nu|v\rangle\langle v|,\qquad (\delta^\Gamma)_+v=0.$$
--   Every separable CPTP channel fixing $\delta$ is mixed LU on the full space. In every product Kraus representation, each nonzero Kraus operator is a complex scalar multiple of a product unitary. The representation-wise clause is stated also for countable representations, with convergence of the Kraus sums explicit.
--
--   This distinguishes rigidity of the given channel from existence of an LU map between endpoints.
-- source:
--   Complete Classification of Reversible Entanglement Transformations of Two Qutrits, arXiv:2610.05234v1, PDF p. 5, Lemma E2: one negative Schmidt-rank-two vector forces global channel rigidity

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2610.05234v1, PDF pp.5–6, Lemma E2: full-space, representation-wise rigidity. -/
theorem singleNegativeVector_rigidity (delta : Joint) (nu : ℝ) (v : Space)
    (hd : IsDensityMatrix delta) (hces : IsCES (operatorRange delta))
    (hr : localRanks (operatorRange delta) = (3, 3)) (hnu : 0 < nu)
    (hv : IsState v) (hsr : (traceRight (pureDensity v)).rank = 2)
    (hJordan : partialTransposeFirst delta = positivePart (partialTransposeFirst delta) -
      (nu : ℂ) • pureDensity v)
    (hortho : act (positivePart (partialTransposeFirst delta)) v = 0)
    (Phi : Superop (Fin 3 × Fin 3) (Fin 3 × Fin 3))
    (hPhi : SeparableChannel Phi) (hfix : Phi delta = delta) :
    MixedLU Phi ∧ ∀ (I : Type) [Countable I] (K : I → Joint),
      CountableRepresentation K Phi → ∀ i, K i ≠ 0 → ScalarProductUnitary (K i) := by sorry

end QAlgorithms.Papers.Independent.Information100.P07

end
