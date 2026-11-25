-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_AdmissibleHermitianColumns_leadingMinor_add_rankOne
-- name    : ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.leadingMinor_add_rankOne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:11:27.205115+00:00
-- url     : https://prove2.me/theorems/ac12be74-e71f-5ffc-a1be-91c19eb48063
-- title:
--   Admissible Hermitian Columns: leading Minor add rank One
-- statement:
--   The Admissible Hermitian Columns construction uses the leading Minor add rank One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/AdmissibleHermitianColumns.lean#L93-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/AdmissibleHermitianColumns.lean#L93-L116

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_AdmissibleHermitianColumns
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.leadingMinor_add_rankOne (A : Matrix (Fin r) (Fin r) ℂ) (u v : Fin r → ℂ) (i : Fin (r + 1))
    (hA : lminor A i ≠ 0) : ∃ κ : ℂ, ∀ t : ℂ, lminor (A + t • vecMulVec u v) i = lminor A i * (1 + t * κ) := by sorry
