-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_finrank_inf_ker
-- name    : ReciprocityTheory.MultiplicativeHeights.wa_finrank_inf_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:47.988586+00:00
-- url     : https://prove2.me/theorems/66b2cd6d-7f69-4c23-83b4-07c4b5d76279
-- title:
--   Multiplicative Heights: wa finrank inf ker
-- statement:
--   The Multiplicative Heights construction uses the wa finrank inf ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean#L63-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean#L63-L83

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

theorem ReciprocityTheory.MultiplicativeHeights.wa_finrank_inf_ker {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V) (f : V →ₗ[K] K) (z : V) (hz : z ∈ W)
    (hfz : f z ≠ 0) : finrank K ↥(W ⊓ LinearMap.ker f) + 1 = finrank K W := by sorry
