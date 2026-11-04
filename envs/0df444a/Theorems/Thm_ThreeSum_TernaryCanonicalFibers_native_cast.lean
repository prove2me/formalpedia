-- Prove2me | Theorems.Thm_ThreeSum_TernaryCanonicalFibers_native_cast
-- name    : ThreeSum.TernaryCanonicalFibers.native_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:38:22.909547+00:00
-- url     : https://prove2.me/theorems/f75e126e-b7d8-4ca5-a502-044e103c9f8e
-- title:
--   Ternary Canonical Fibers: native cast
-- statement:
--   The Ternary Canonical Fibers construction uses the native cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalFibers.lean#L75-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalFibers.lean#L75-L81

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCanonicalFibers
open Finset TernaryFixedDictionaries TernaryCanonicalDictionaries TernaryJointType TernaryCoverLocal
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem ThreeSum.TernaryCanonicalFibers.native_cast (right : Bool)
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) :
    ((native right maps r : ℤ) : ZMod p)=
      if right then rightNative maps r else leftNative maps r := by sorry
