-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_herm_Mmat
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.herm_Mmat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:22:45.180802+00:00
-- url     : https://prove2.me/theorems/e5ad649c-5209-43ff-b6ca-33abfdd25763
-- title:
--   Data: herm Mmat
-- statement:
--   The Data construction uses the herm Mmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MmatMulVec.lean#L129-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MmatMulVec.lean#L129-L138

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.herm_Mmat (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (β : Matrix (Fin 2) (Fin 2) E) (hβ : ∀ i k, cc (β i k) = β k i) (v w : Fin r → E) :
    herm X.Gm (X.Mmat u β *ᵥ v) (X.Mmat u β *ᵥ w) = herm X.Gm v w := by sorry
