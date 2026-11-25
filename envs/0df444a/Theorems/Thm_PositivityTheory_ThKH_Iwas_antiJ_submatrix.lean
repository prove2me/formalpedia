-- Prove2me | Theorems.Thm_PositivityTheory_ThKH_Iwas_antiJ_submatrix
-- name    : PositivityTheory.ThKH.Iwas.antiJ_submatrix
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:06:21.385598+00:00
-- url     : https://prove2.me/theorems/c061d345-52e9-5d8f-935a-5162f857e112
-- title:
--   Iwas: anti J submatrix
-- statement:
--   The Iwas construction uses the anti J submatrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/IwasLoc.lean#L13-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/IwasLoc.lean#L13-L33

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_IwasLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Iwas
open Matrix Formalism.UG Formalism.UG.P GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

theorem PositivityTheory.ThKH.Iwas.antiJ_submatrix (L : Type) [Field L] (m : ℕ) :
    (antiJ L (m + m)).submatrix (ee m) (ee m) = Wm L (Fin m) := by sorry
