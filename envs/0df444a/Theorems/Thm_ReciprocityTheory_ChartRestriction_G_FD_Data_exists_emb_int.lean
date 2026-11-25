-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_exists_emb_int
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.exists_emb_int
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:12:05.387997+00:00
-- url     : https://prove2.me/theorems/ee34e94d-46e3-5e7b-ba98-c9fe6dc5c284
-- title:
--   Data: exists emb int
-- statement:
--   The Data construction uses the exists emb int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ConjugateConjugate.lean#L175-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ConjugateConjugate.lean#L175-L214

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.exists_emb_int (z : X.Ψ → ℂ) (g : ℕ) (hg : 0 < g)
    (hz : ∀ γ : 𝓞 E, ∃ k : ℤ, ((2 * g * (NumberField.discr E).natAbs : ℕ) : ℝ) *
      (∑ τ : X.Ψ, z τ * τ.1 (γ : E)).re = k) :
    ∃ ω : E, (∀ τ : X.Ψ, z τ = τ.1 ω) ∧
      IsIntegral ℤ (((g * (NumberField.discr E).natAbs ^ 2 : ℕ) : E) * ω) := by sorry
