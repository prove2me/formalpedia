-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P32_antisymmetric_strict_separation
-- name    : QAlgorithms.Papers.Independent.Gap48.P32.antisymmetric_strict_separation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:31:34.012247+00:00
-- url     : https://prove2.me/theorems/04d7d981-59ee-482e-9c09-4e9a24b12b28
-- title:
--   Two-qutrit antisymmetric strict separation
-- statement:
--   All registers are finite and have positive dimension. Density matrices are positive semidefinite with trace one, all pure vectors have norm one, and entropy is in bits. Write $S$ for von Neumann entropy, $I(A;B)=S(A)+S(B)-S(AB)$, and $I(A;B|E)=S(AE)+S(BE)-S(E)-S(ABE)$. The squashed entanglement $E_{\mathrm{sq}}(\rho)$ is the infimum of $I(A;B|E)/2$ over every finite quantum extension of $\rho$, with no common dimension cap or attainment assumption. All marginals below are actual partial traces.
--
--   On $\mathbb C^3\otimes\mathbb C^3$, let $F|i,j\rangle=|j,i\rangle$ and $\sigma=(I-F)/6$, the uniform mixture of the three normalized antisymmetric basis vectors. Then $$E_{\mathrm{sq}}(\sigma)\le\frac{\log_2 3}{2}<1=E_F(\sigma)=E_C(\sigma).$$ In particular, squashed entanglement is strictly smaller than both formation and cost on this explicit state. The source credits the two unit formation/cost values to Yura [31].
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, PDF p. 4, §II, Example 9

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

/-- PDF p.4, Example 9: original squashed upper bound and strict separation;
the two unit formation/cost values are background explicitly credited to Yura [31]. -/
theorem antisymmetric_strict_separation :
    sq antisymmetricQutrit ≤ Real.logb 2 3 / 2 ∧
    Real.logb 2 3 / 2 < 1 ∧
    ef antisymmetricQutrit = 1 ∧
    QAlgorithms.Papers.Independent.Dependency50.P42.entanglementCost
      QAlgorithms.Papers.Independent.Dependency50.P42.paperBures antisymmetricQutrit = 1 ∧
    sq antisymmetricQutrit < ef antisymmetricQutrit ∧
    sq antisymmetricQutrit < QAlgorithms.Papers.Independent.Dependency50.P42.entanglementCost
      QAlgorithms.Papers.Independent.Dependency50.P42.paperBures antisymmetricQutrit := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P32
