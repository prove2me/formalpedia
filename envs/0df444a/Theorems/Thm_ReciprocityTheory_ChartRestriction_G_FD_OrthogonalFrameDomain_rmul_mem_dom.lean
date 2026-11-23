-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthogonalFrameDomain_rmul_mem_dom
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:22.969864+00:00
-- url     : https://prove2.me/theorems/b1db0904-86ee-452a-9450-262a51b88cff
-- title:
--   Orthogonal Frame Domain: rmul mem dom
-- statement:
--   The Orthogonal Frame Domain construction uses the rmul mem dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/OrthogonalFrameDomain.lean#L23-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/OrthogonalFrameDomain.lean#L23-L82

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LogDOfPosBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom {z b : Frame X.Ψ r} (hz : z ∈ X.dom) (hb : b ∈ Bor X.Ψ r) : rmul z b ∈ X.dom := by sorry
