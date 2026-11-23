-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_exists_norm_one_of_pair
-- name    : ReciprocityTheory.ChartRestriction.L3.WA.exists_norm_one_of_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:21.818894+00:00
-- url     : https://prove2.me/theorems/ae81ba6f-3cd7-441f-b136-c8645beb0447
-- title:
--   WA: exists norm one of pair
-- statement:
--   The WA construction uses the exists norm one of pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsNormOneOfPair.lean#L84-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsNormOneOfPair.lean#L84-L141

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsNormOneOfPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type*} [Field K] [StarRing K]
variable {S : Subring K}
variable {V : Type*} [AddCommGroup V] [Module K V]

theorem ReciprocityTheory.ChartRestriction.L3.WA.exists_norm_one_of_pair (hS : IsHermSemilocal S) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    {y w : V} {a : K} (ha : a ∈ S) (ha0 : a ≠ 0) (hy : h y y = star a * a) (hyw : h y w = 1)
    (hw : h w w ∈ S) :
    ∃ c ∈ S, ∃ d ∈ S, h (c • w + d • y) (c • w + d • y) = 1 := by sorry
