-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_zmat_unitary
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.zmat_unitary
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:22:13.078567+00:00
-- url     : https://prove2.me/theorems/cf1bb2f3-7019-4070-bc6c-c72f589e3229
-- title:
--   Data: zmat unitary
-- statement:
--   The Data construction uses the zmat unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SpanColsMul.lean#L77-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SpanColsMul.lean#L77-L89

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.zmat_unitary (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (τ : X.Ψ) (v w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.zmat u b τ *ᵥ v) (X.zmat u b τ *ᵥ w) = hermC τ.1 X.Gm v w := by sorry
