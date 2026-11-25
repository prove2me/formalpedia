-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_h_smul_right
-- name    : ReciprocityTheory.MultiplicativeHeights.approxB_h_smul_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:03:22.990298+00:00
-- url     : https://prove2.me/theorems/6a6777d4-62d8-59c0-8ff0-e036c2f928d2
-- title:
--   Multiplicative Heights: approx B h smul right
-- statement:
--   The Multiplicative Heights construction uses the approx B h smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisB.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisB.lean#L14-L22

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

theorem ReciprocityTheory.MultiplicativeHeights.approxB_h_smul_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) (a : K) : S.h x (a • y) = a * S.h x y := by sorry
