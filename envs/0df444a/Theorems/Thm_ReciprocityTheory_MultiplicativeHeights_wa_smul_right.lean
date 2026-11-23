-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_smul_right
-- name    : ReciprocityTheory.MultiplicativeHeights.wa_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:14.529632+00:00
-- url     : https://prove2.me/theorems/f070aae7-5992-400d-87ef-d279dfadf949
-- title:
--   Multiplicative Heights: wa smul right
-- statement:
--   The Multiplicative Heights construction uses the wa smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean#L32-L35

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module

theorem ReciprocityTheory.MultiplicativeHeights.wa_smul_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (x y : Fin r → K) : S.h x (a • y) = a * S.h x y := by sorry
