-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_CG_pi_cont_supp
-- name    : PositivityTheory.Rg.BcB.CG.pi_cont_supp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:01.158909+00:00
-- url     : https://prove2.me/theorems/c6b20a59-b8b3-4a0b-9643-cb973520afa7
-- title:
--   CG: pi cont supp
-- statement:
--   The CG construction uses the pi cont supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L123-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L123-L141

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

theorem PositivityTheory.Rg.BcB.CG.pi_cont_supp {ι : Type} [Fintype ι] [DecidableEq ι] {Idx : ι → Type} [∀ v, Fintype (Idx v)]
    (e : ∀ v, X → Idx v → Idx v → ℂ) (u : (∀ v, Idx v) → (ι → X) → ℂ) (I : ∀ v, Idx v)
    (he : ∀ v a b, Continuous (fun t => e v t a b) ∧ HasCompactSupport (fun t => e v t a b))
    (hu : ∀ J, Continuous (u J)) :
    Continuous (fun y : ι → X => ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y) ∧
      HasCompactSupport (fun y : ι → X => ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y) := by sorry
