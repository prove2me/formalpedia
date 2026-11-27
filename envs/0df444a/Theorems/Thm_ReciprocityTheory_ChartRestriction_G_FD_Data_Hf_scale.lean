-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_scale
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.Hf_scale
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:12:56.87094+00:00
-- url     : https://prove2.me/theorems/b60a34c7-d960-480d-a72e-b33718370948
-- title:
--   Data: Hf scale
-- statement:
--   The Data construction uses the Hf scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowFixesComplementOfIsotropic.lean#L114-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowFixesComplementOfIsotropic.lean#L114-L179

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowFixesComplementOfIsotropic
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
variable (ξ : Fin r → E) (τ : X.Ψ)

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.Hf_scale (hiso : hermC τ.1 X.Gm (emb τ.1 ξ) (emb τ.1 ξ) = 0) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hxs : X.flow ξ s x ∈ X.dom) :
    ∃ k : ℂ, k ≠ 0 ∧ ∀ v : Fin r → ℂ, hermC τ.1 X.Gm v (emb τ.1 ξ) = 0 →
      X.Hf x τ v (emb τ.1 ξ) = k * X.Hf (X.flow ξ s x) τ v (emb τ.1 ξ) := by sorry
