-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_CG_pi_iter
-- name    : PositivityTheory.Rg.BcB.CG.pi_iter
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:51:05.48651+00:00
-- url     : https://prove2.me/theorems/c0abc8a0-0e0c-4448-8d02-be964e9240be
-- title:
--   CG: pi iter
-- statement:
--   The CG construction uses the pi iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L254-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L254-L262

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PActPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG
variable {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
variable [One X]

theorem PositivityTheory.Rg.BcB.CG.pi_iter (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Idx : ι → Type) [∀ v, Fintype (Idx v)] [∀ v, DecidableEq (Idx v)]
    (e : ∀ v, X → Idx v → Idx v → ℂ) (val : ι → ℂ) (u : (∀ v, Idx v) → (ι → X) → ℂ) (I : ∀ v, Idx v)
    (he : ∀ v a b, Continuous (fun t => e v t a b) ∧ HasCompactSupport (fun t => e v t a b))
    (hu : ∀ J, Continuous (u J))
    (hloc : ∀ v J y, ∑ j, ∫ t, e v t (J v) j * u (Function.update J v j) (Function.update y v t) ∂μ =
      val v * u J (Function.update y v 1)) :
    ∫ y, ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y ∂(Measure.pi fun _ => μ) = (∏ v, val v) * u I 1 := by sorry
