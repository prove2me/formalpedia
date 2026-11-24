-- Prove2me | Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity_GlW_comm__671fb396e97c
-- name    : P2M_Formalism_GM_DimensionMonotonicity_GlW_comm__671fb396e97c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:27:21.652734+00:00
-- url     : https://prove2.me/theorems/53da1701-6630-4e8f-ada0-2bd9de194b5a
-- title:
--   P2 M Formalism GM Dimension Monotonicity Gl W comm  671fb396e97c: P2 M Formalism GM Dimension Monotonicity Gl W comm  671fb396e97c
-- statement:
--   The P2 M Formalism GM Dimension Monotonicity Gl W comm  671fb396e97c construction uses the P2 M Formalism GM Dimension Monotonicity Gl W comm  671fb396e97c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L153-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L153-L156

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open Finset
open Formalism.GM.DimensionMonotonicity.GlW
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

theorem P2M_Formalism_GM_DimensionMonotonicity_GlW_comm__671fb396e97c (a b c d : Fin r) (x : V) : G.E a b (G.E c d x) = G.E c d (G.E a b x) +
    ((if b = c then G.E a d x else 0) - (if d = a then G.E c b x else 0)) := by sorry

alias «Formalism».«GM».«DimensionMonotonicity».«GlW».«comm'» := P2M_Formalism_GM_DimensionMonotonicity_GlW_comm__671fb396e97c
