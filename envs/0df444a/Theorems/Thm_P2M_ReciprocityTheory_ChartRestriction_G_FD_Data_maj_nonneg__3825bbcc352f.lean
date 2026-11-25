-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_nonneg__3825bbcc352f
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_nonneg__3825bbcc352f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:41.214811+00:00
-- url     : https://prove2.me/theorems/f38a183f-0207-58ea-9a80-ffa10fba2c47
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Data maj nonneg  3825bbcc352f: P2 M Reciprocity Theory Chart Restriction G FD Data maj nonneg  3825bbcc352f
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Data maj nonneg  3825bbcc352f construction uses the P2 M Reciprocity Theory Chart Restriction G FD Data maj nonneg  3825bbcc352f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentSubOneMajorantBound.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentSubOneMajorantBound.lean#L52-L56

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
variable {x : Frame X.Ψ r} {τ : X.Ψ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_nonneg__3825bbcc352f (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ))
    (hpos : ∀ v, v ≠ 0 → 0 < X.maj x τ v) (v : Fin r → ℂ) : 0 ≤ X.maj x τ v := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«Data».«maj_nonneg'» := P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_nonneg__3825bbcc352f
