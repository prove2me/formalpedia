-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_exists_isom_fix
-- name    : ReciprocityTheory.ChartRestriction.L3.WA.exists_isom_fix
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:47:08.638481+00:00
-- url     : https://prove2.me/theorems/7b74c369-6e3e-5aa2-bfd3-7a88bf8661fd
-- title:
--   WA: exists isom fix
-- statement:
--   The WA construction uses the exists isom fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsIsomFix.lean#L46-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsIsomFix.lean#L46-L79

import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsIsomFix
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

theorem ReciprocityTheory.ChartRestriction.L3.WA.exists_isom_fix {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0)
    {x y : V} (hx : h x x = 1) (hy : h y y = 1) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = y ∧ ∀ v, h x v = 0 → h y v = 0 → τ v = v := by sorry
