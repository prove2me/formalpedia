-- Prove2me | Theorems.Thm_PositivityTheory_ThKH_Iwas_inv_apply_of_iso
-- name    : PositivityTheory.ThKH.Iwas.inv_apply_of_iso
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:06:37.117379+00:00
-- url     : https://prove2.me/theorems/559c02f3-5934-5b30-9e4e-231ed5d64fa5
-- title:
--   Iwas: inv apply of iso
-- statement:
--   The Iwas construction uses the inv apply of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/IwasLoc.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/IwasLoc.lean#L65-L69

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
variable {L : Type} [Field L] {c : L →+* L} {β : Type} [Fintype β] [DecidableEq β]

theorem PositivityTheory.ThKH.Iwas.inv_apply_of_iso (hc : ∀ x, c (c x) = x) {M N : Matrix (β ⊕ β) (β ⊕ β) L} (h : Iso c (Wm L β) (Wm L β) M)
    (hN : M * N = 1) (i j : β ⊕ β) : N i j = c (M j.swap i.swap) := by sorry
