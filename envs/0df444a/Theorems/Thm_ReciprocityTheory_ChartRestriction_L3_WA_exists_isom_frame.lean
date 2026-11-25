-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_exists_isom_frame
-- name    : ReciprocityTheory.ChartRestriction.L3.WA.exists_isom_frame
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:47:07.196893+00:00
-- url     : https://prove2.me/theorems/0b5e644a-1424-471d-8966-16b3a7240cb6
-- title:
--   WA: exists isom frame
-- statement:
--   The WA construction uses the exists isom frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsIsomFrame.lean#L83-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsIsomFrame.lean#L83-L117

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

theorem ReciprocityTheory.ChartRestriction.L3.WA.exists_isom_frame (hS : IsHermSemilocal S) (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0)
    (hM : IsSelfDualMod S h M) {n : ℕ} (e : Fin n → V)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i, g (e i) ∈ M := by sorry
