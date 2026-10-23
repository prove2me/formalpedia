-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P32_entropy_lower_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P32.entropy_lower_bound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:34:25.705154+00:00
-- url     : https://prove2.me/theorems/0fb25a21-bbef-42fc-8abd-28f3799ff1a7
-- title:
--   Explicit entropy lower bound
-- statement:
--   All registers are finite and have positive dimension. Density matrices are positive semidefinite with trace one, all pure vectors have norm one, and entropy is in bits. Write $S$ for von Neumann entropy, $I(A;B)=S(A)+S(B)-S(AB)$, and $I(A;B|E)=S(AE)+S(BE)-S(E)-S(ABE)$. The squashed entanglement $E_{\mathrm{sq}}(\rho)$ is the infimum of $I(A;B|E)/2$ over every finite quantum extension of $\rho$, with no common dimension cap or attainment assumption. All marginals below are actual partial traces.
--
--   Every bipartite density matrix $\rho$ satisfies $$\frac{I(A;B)_\rho-S(\rho)}{2}\le E_{\mathrm{sq}}(\rho).$$ Equivalently the numerator is $S(\rho^A)+S(\rho^B)-2S(\rho)$. This is the source’s explicit entropy lower bound.
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, PDF p. 5, §II, Corollary 12

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

section Bipartite

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [instAne : Nonempty A] [instBne : Nonempty B]

include instAne instBne

/-- PDF p.5, Corollary 12: the printed parentheses put BOTH terms under 1/2. -/
theorem entropy_lower_bound (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) : (mi rho - vnEntropy rho) / 2 ≤ sq rho := by sorry

end Bipartite

end

end QAlgorithms.Papers.Independent.Gap48.P32
