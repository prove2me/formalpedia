-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_kE_dv
-- name    : PositivityTheory.ThKF0.Chr.kE_dv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:23.297526+00:00
-- url     : https://prove2.me/theorems/bb0eeadc-45ce-4da2-b28f-acfbc33e483d
-- title:
--   Chr: k E dv
-- statement:
--   The Chr construction uses the k E dv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L58-L61

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ κ₁ : Type}

theorem PositivityTheory.ThKF0.Chr.kE_dv (p : κ → Prop) [DecidablePred p] (w w' : V R κ) : kE R p (dv w w') =
    (Sum.elim (w.1 - w'.1) fun k => if p k then w.2 k - w'.2 k else w'.1 k,
      Sum.elim w.2 fun k => if p k then -w'.1 k else w.2 k - w'.2 k) := by sorry
