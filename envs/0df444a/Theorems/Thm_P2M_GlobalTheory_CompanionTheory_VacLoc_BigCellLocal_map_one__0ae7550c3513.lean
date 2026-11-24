-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_map_one__0ae7550c3513
-- name    : P2M_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_map_one__0ae7550c3513
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:55.202737+00:00
-- url     : https://prove2.me/theorems/4206f629-9548-4c06-81fb-c9984ede8a23
-- title:
--   P2 M Global Theory Companion Theory Vac Loc Big Cell Local map one  0ae7550c3513: P2 M Global Theory Companion Theory Vac Loc Big Cell Local map one  0ae7550c3513
-- statement:
--   The P2 M Global Theory Companion Theory Vac Loc Big Cell Local map one  0ae7550c3513 construction uses the P2 M Global Theory Companion Theory Vac Loc Big Cell Local map one  0ae7550c3513 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BigCellLocal.lean#L52-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BigCellLocal.lean#L52-L52

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsSkewOfDiagonal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
variable {A : Type} [CommRing A] {σ : A →+* A} {β : Type} [Fintype β] [DecidableEq β]

theorem P2M_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_map_one__0ae7550c3513 : (1 : Matrix β β A).map σ = 1 := by sorry

alias «GlobalTheory».«CompanionTheory».«VacLoc».«BigCellLocal».«map_one'» := P2M_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_map_one__0ae7550c3513
