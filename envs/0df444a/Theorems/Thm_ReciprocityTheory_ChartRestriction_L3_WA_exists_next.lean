-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_exists_next
-- name    : ReciprocityTheory.ChartRestriction.L3.WA.exists_next
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:46:59.689197+00:00
-- url     : https://prove2.me/theorems/4ee816a3-7bb3-5d22-b4e7-c06055803eea
-- title:
--   WA: exists next
-- statement:
--   The WA construction uses the exists next property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsIsomFrame.lean#L18-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsIsomFrame.lean#L18-L81

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsNormOneOfPair
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsIsomFix
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsIsomFrame
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
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}

theorem ReciprocityTheory.ChartRestriction.L3.WA.exists_next (hS : IsHermSemilocal S) (hs : h.IsSymm) (hM : IsSelfDualMod S h M)
    {ι : Type*} [DecidableEq ι] (x : ι → V) (hx : ∀ i j, h (x i) (x j) = if i = j then 1 else 0)
    (s : Finset ι) (hxM : ∀ i ∈ s, x i ∈ M) (j : ι) (hj : j ∉ s) :
    ∃ z ∈ M, h z z = 1 ∧ ∀ i ∈ s, h (x i) z = 0 := by sorry
