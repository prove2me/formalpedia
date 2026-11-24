-- Prove2me | Theorems.Thm_PositivityTheory_ThKH_Iwas_iso_iff_cT
-- name    : PositivityTheory.ThKH.Iwas.iso_iff_cT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:30.556827+00:00
-- url     : https://prove2.me/theorems/56845ab1-4bdd-48a9-8474-35b6735a3e5d
-- title:
--   Iwas: iso iff c T
-- statement:
--   The Iwas construction uses the iso iff c T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/IwasLoc.lean#L43-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/IwasLoc.lean#L43-L55

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

theorem PositivityTheory.ThKH.Iwas.iso_iff_cT (hc : ∀ x, c (c x) = x) (M : Matrix (β ⊕ β) (β ⊕ β) L) :
    Iso c (Wm L β) (Wm L β) M ↔ cT c M * Wm L β * M = Wm L β := by sorry
