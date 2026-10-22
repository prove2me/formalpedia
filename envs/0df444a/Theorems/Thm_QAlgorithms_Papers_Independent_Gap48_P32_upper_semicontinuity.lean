-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P32_upper_semicontinuity
-- name    : QAlgorithms.Papers.Independent.Gap48.P32.upper_semicontinuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:38:17.556392+00:00
-- url     : https://prove2.me/theorems/1e53dfc4-2bac-4293-b375-233f797be8cd
-- title:
--   Upper semicontinuity on the state set
-- statement:
--   All registers are finite and have positive dimension. Density matrices are positive semidefinite with trace one, all pure vectors have norm one, and entropy is in bits. Write $S$ for von Neumann entropy, $I(A;B)=S(A)+S(B)-S(AB)$, and $I(A;B|E)=S(AE)+S(BE)-S(E)-S(ABE)$. The squashed entanglement $E_{\mathrm{sq}}(\rho)$ is the infimum of $I(A;B|E)/2$ over every finite quantum extension of $\rho$, with no common dimension cap or attainment assumption. All marginals below are actual partial traces.
--
--   At each state $\rho$ and for every $\epsilon>0$, there is $\delta>0$ such that every state $\sigma$ with $\|\sigma-\rho\|_1<\delta$ satisfies $$E_{\mathrm{sq}}(\sigma)<E_{\mathrm{sq}}(\rho)+\epsilon.$$ This is upper semicontinuity relative to normalized states, including boundary points.
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, PDF p. 6, §IV, Remark 15

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

/-- PDF p.6, Remark 15: upper semicontinuity on normalized states.
This does not assert a generic implication from convexity at boundary points. -/
theorem upper_semicontinuity (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) :
    ∀ epsilon > (0 : ℝ), ∃ delta > (0 : ℝ),
      ∀ sigma : Matrix (A × B) (A × B) ℂ, IsDensityMatrix sigma →
        traceNorm (sigma-rho) < delta → sq sigma < sq rho + epsilon := by sorry

end Bipartite

end

end QAlgorithms.Papers.Independent.Gap48.P32
