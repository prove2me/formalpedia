-- Prove2me | Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity_glAct_wh__8320259c7632
-- name    : P2M_Formalism_GM_DimensionMonotonicity_glAct_wh__8320259c7632
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:44.243266+00:00
-- url     : https://prove2.me/theorems/eef72339-ba16-4bca-a2dc-3cab50ffca37
-- title:
--   P2 M Formalism GM Dimension Monotonicity gl Act wh  8320259c7632: P2 M Formalism GM Dimension Monotonicity gl Act wh  8320259c7632
-- statement:
--   The P2 M Formalism GM Dimension Monotonicity gl Act wh  8320259c7632 construction uses the P2 M Formalism GM Dimension Monotonicity gl Act wh  8320259c7632 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1387-L1420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1387-L1420

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

theorem P2M_Formalism_GM_DimensionMonotonicity_glAct_wh__8320259c7632 (LL : Letters N) {j J : ℕ} (hjJ : j ≤ J) (a b : Fin r) {ν : Fin r → ℤ}
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν) :
    glAct p LL j a b x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) (ν + dl a b) := by sorry

alias «Formalism».«GM».«DimensionMonotonicity».«glAct_wh'» := P2M_Formalism_GM_DimensionMonotonicity_glAct_wh__8320259c7632
