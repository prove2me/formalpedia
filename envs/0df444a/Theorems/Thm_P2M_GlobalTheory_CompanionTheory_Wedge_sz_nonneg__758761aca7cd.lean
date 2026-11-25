-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Wedge_sz_nonneg__758761aca7cd
-- name    : P2M_GlobalTheory_CompanionTheory_Wedge_sz_nonneg__758761aca7cd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:08.320718+00:00
-- url     : https://prove2.me/theorems/8bdb0a8d-7362-41c0-a3f5-c69614f968a4
-- title:
--   P2 M Global Theory Companion Theory Wedge sz nonneg  758761aca7cd: P2 M Global Theory Companion Theory Wedge sz nonneg  758761aca7cd
-- statement:
--   The P2 M Global Theory Companion Theory Wedge sz nonneg  758761aca7cd construction uses the P2 M Global Theory Companion Theory Wedge sz nonneg  758761aca7cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L31-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L31-L31

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundFinitePlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
variable {K ι ι' κ κ' : Type} [NormedField K]

theorem P2M_GlobalTheory_CompanionTheory_Wedge_sz_nonneg__758761aca7cd (g : Matrix ι κ K) : 0 ≤ sz g := by sorry

alias «GlobalTheory».«CompanionTheory».«Wedge».«sz_nonneg'» := P2M_GlobalTheory_CompanionTheory_Wedge_sz_nonneg__758761aca7cd
