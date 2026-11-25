-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_hasFDerivAt_integral_K
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CasPsB.hasFDerivAt_integral_K
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:44:32.792928+00:00
-- url     : https://prove2.me/theorems/6d6604a6-e7c7-430e-a8ba-73a972e31784
-- title:
--   Cas Ps B: has FDeriv At integral K
-- statement:
--   The Cas Ps B construction uses the has FDeriv At integral K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsB.lean#L24-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsB.lean#L24-L58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
local notation "𝕄" => Fin n → Fin n → ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.CasPsB.hasFDerivAt_integral_K [CompactSpace (KG ε)] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] [SecondCountableTopologyEither (KG ε) E]
    [SecondCountableTopologyEither (KG ε) (𝕄 →L[ℂ] E)] {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U)
    (F : Matrix (Fin n) (Fin n) ℂ → KG ε → E) (F' : Matrix (Fin n) (Fin n) ℂ → KG ε → (𝕄 →L[ℂ] E))
    (hF : ContinuousOn (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε => F p.1 p.2) (U ×ˢ Set.univ))
    (hF' : ContinuousOn (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε => F' p.1 p.2) (U ×ˢ Set.univ))
    (hd : ∀ x ∈ U, ∀ k, HasFDerivAt (fun y : 𝕄 => F y k) (F' x k) x)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ U) :
    HasFDerivAt (fun x : 𝕄 => ∫ k, F x k ∂(muK ε)) (∫ k, F' z k ∂(muK ε)) z := by sorry
