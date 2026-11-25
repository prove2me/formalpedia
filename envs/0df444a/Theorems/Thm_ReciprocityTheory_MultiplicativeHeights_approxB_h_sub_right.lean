-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_h_sub_right
-- name    : ReciprocityTheory.MultiplicativeHeights.approxB_h_sub_right
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:03:57.622979+00:00
-- url     : https://prove2.me/theorems/11648cf2-fc6e-4dfb-84b5-0d1e3ac7a5ea
-- title:
--   Multiplicative Heights: approx B h sub right
-- statement:
--   The Multiplicative Heights construction uses the approx B h sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisB.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisB.lean#L24-L27

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisB
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
open Matrix NumberField ComplexConjugate

theorem ReciprocityTheory.MultiplicativeHeights.approxB_h_sub_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y z : Fin r → K) : S.h x (y - z) = S.h x y - S.h x z := by sorry
