-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthogonalComplementLines_ppos_sub
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthogonalComplementLines.ppos_sub
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:18:55.208392+00:00
-- url     : https://prove2.me/theorems/ec09829f-de9d-4790-b46d-05bb3e47c6e7
-- title:
--   Orthogonal Complement Lines: ppos sub
-- statement:
--   The Orthogonal Complement Lines construction uses the ppos sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/OrthogonalComplementLines.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/OrthogonalComplementLines.lean#L24-L26

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceFormIndependence
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalComplementLines
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthogonalComplementLines
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthogonalComplementLines.ppos_sub (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.ppos x τ (u - v) = X.ppos x τ u - X.ppos x τ v := by sorry
