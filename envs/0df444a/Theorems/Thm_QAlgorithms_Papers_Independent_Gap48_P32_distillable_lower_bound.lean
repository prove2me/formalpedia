-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P32_distillable_lower_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P32.distillable_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:32:22.413904+00:00
-- url     : https://prove2.me/theorems/d6bd55c8-a4ea-461d-af05-863573cd4ba1
-- title:
--   Two-way LOCC distillable-entanglement lower bound
-- statement:
--   All registers are finite and have positive dimension. Density matrices are positive semidefinite with trace one, all pure vectors have norm one, and entropy is in bits. Write $S$ for von Neumann entropy, $I(A;B)=S(A)+S(B)-S(AB)$, and $I(A;B|E)=S(AE)+S(BE)-S(E)-S(ABE)$. The squashed entanglement $E_{\mathrm{sq}}(\rho)$ is the infimum of $I(A;B|E)/2$ over every finite quantum extension of $\rho$, with no common dimension cap or attainment assumption. All marginals below are actual partial traces.
--
--   Let $E_D(\rho)$ be the supremum of nonnegative achievable two-way LOCC distillation rates. A rate $R$ is achievable if, for every $\epsilon,\delta>0$ and all sufficiently large positive $n$, a finite adaptive unconditional LOCC protocol transforms $\rho^{\otimes n}$ into a state within full trace norm $\epsilon$ of a maximally entangled state of some positive Schmidt rank $l$, with $\log_2l\ge n(R-\delta)$. Then $$E_D(\rho)\le E_{\mathrm{sq}}(\rho).$$ This is an operational upper bound on distillation with unrestricted two-way classical communication.
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, PDF p. 4, §II, Proposition 10

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P32

namespace QAlgorithms.Papers.Independent.Gap48.P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

local notation "sq" => QAlgorithms.Papers.Independent.Dependency50.P19.squashed

local notation "cmi" => QAlgorithms.Papers.Independent.Dependency50.P19.conditionalMutual

local notation "mi" => QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation

local notation "ef" => QAlgorithms.Papers.Independent.Information100.P08.formation

-- Reuse exact accepted generic tensor pairing and partial traces.

open QAlgorithms.Papers.Independent.Next46.P42 (regroupProduct)

open QAlgorithms.Papers.Independent.Information100.P08 (firstPair secondPair)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

/-- PDF p.4, Proposition 10: the full two-way LOCC twoWayDistillable entanglement,
not the accepted no-communication or PPT relaxations, is bounded by E_sq. -/
theorem distillable_lower_bound (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hrho : IsDensityMatrix rho) :
    twoWayDistillable rho ≤ sq rho := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P32
