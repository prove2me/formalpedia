-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_flowV_uvec
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.flowV_uvec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:00.662796+00:00
-- url     : https://prove2.me/theorems/6f028453-2b7b-4669-87a3-2446b0a51c17
-- title:
--   Data: flow V uvec
-- statement:
--   The Data construction uses the flow V uvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SpanColsMul.lean#L136-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SpanColsMul.lean#L136-L149

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

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.flowV_uvec (u : Fin 2 → Fin r → E) (a : X.Ψ → Fin 2 → ℂ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    X.flowV (X.uvec u a) s x = X.Zb u (fun τ i k => s τ * a τ i * conj (a τ k)) x := by sorry
