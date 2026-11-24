-- Prove2me | Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity__F_val_6b0203f3e58f
-- name    : P2M_Formalism_GM_DimensionMonotonicity__F_val_6b0203f3e58f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:19.61412+00:00
-- url     : https://prove2.me/theorems/49c64904-0910-4af3-baac-24f055316258
-- title:
--   P2 M Formalism GM Dimension Monotonicity  F val 6b0203f3e58f: P2 M Formalism GM Dimension Monotonicity  F val 6b0203f3e58f
-- statement:
--   The P2 M Formalism GM Dimension Monotonicity  F val 6b0203f3e58f construction uses the P2 M Formalism GM Dimension Monotonicity  F val 6b0203f3e58f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1963-L1967
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1963-L1967

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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem P2M_Formalism_GM_DimensionMonotonicity__F_val_6b0203f3e58f [NeZero N] {K : ℕ} (hK : K + 1 ≤ N) (a : Fin (K + 1)) : ((ιF N K a) : ℕ) = a := by sorry

alias «Formalism».«GM».«DimensionMonotonicity».«ιF_val» := P2M_Formalism_GM_DimensionMonotonicity__F_val_6b0203f3e58f
