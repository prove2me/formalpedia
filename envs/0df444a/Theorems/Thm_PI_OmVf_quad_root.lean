-- Prove2me | Theorems.Thm_PI_OmVf_quad_root
-- name    : PI.OmVf.quad_root
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:02:21.38598+00:00
-- url     : https://prove2.me/theorems/e111ad14-cb2f-4f2b-9022-8199fcd3d848
-- title:
--   Om Vf: quad root
-- statement:
--   The Om Vf construction uses the quad root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/QuadRoot.lean#L9-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/QuadRoot.lean#L9-L29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_QuadRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open PI PI.OmVf

theorem PI.OmVf.quad_root {R : Type*} [CommRing R] [HenselianLocalRing R] (A B K : R) (hA : A ∈ maximalIdeal R)
    (hB : IsUnit B) : ∃ s : R, A * s ^ 2 + B * s + K = 0 := by sorry
