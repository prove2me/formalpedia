-- Prove2me | Theorems.Thm_PI_WAU_coord_incl
-- name    : PI.WAU.coord_incl
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:44:00.387739+00:00
-- url     : https://prove2.me/theorems/4498ebbc-6db9-4fb5-9666-4953fc2555d4
-- title:
--   WAU: coord incl
-- statement:
--   The WAU construction uses the coord incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/CoordTmulOneMul.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/CoordTmulOneMul.lean#L55-L58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open scoped TensorProduct
variable {F E B : Type} [Field F] [Field E] [Algebra F E] [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

theorem PI.WAU.coord_incl (e : E) :
    coord b (Algebra.TensorProduct.includeLeftRingHom (R := F) (B := B) e) = fun k => algebraMap F B (b.repr e k) := by sorry
