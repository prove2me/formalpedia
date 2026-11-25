-- Prove2me | Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity__F_inj_224398c1e583
-- name    : P2M_Formalism_GM_DimensionMonotonicity__F_inj_224398c1e583
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:26.11642+00:00
-- url     : https://prove2.me/theorems/0cf1d01d-f26e-4499-833b-4438fd24f521
-- title:
--   P2 M Formalism GM Dimension Monotonicity  F inj 224398c1e583: P2 M Formalism GM Dimension Monotonicity  F inj 224398c1e583
-- statement:
--   The P2 M Formalism GM Dimension Monotonicity  F inj 224398c1e583 construction uses the P2 M Formalism GM Dimension Monotonicity  F inj 224398c1e583 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1969-L1972
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1969-L1972

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

theorem P2M_Formalism_GM_DimensionMonotonicity__F_inj_224398c1e583 [NeZero N] {K : ℕ} (hK : K + 1 ≤ N) : Function.Injective (ιF N K) := by sorry

alias «Formalism».«GM».«DimensionMonotonicity».«ιF_inj» := P2M_Formalism_GM_DimensionMonotonicity__F_inj_224398c1e583
