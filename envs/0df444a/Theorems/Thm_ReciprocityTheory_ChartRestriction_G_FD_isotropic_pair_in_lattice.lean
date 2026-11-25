-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_isotropic_pair_in_lattice
-- name    : ReciprocityTheory.ChartRestriction.G.FD.isotropic_pair_in_lattice
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:21:19.589052+00:00
-- url     : https://prove2.me/theorems/606b8a8d-d08f-4a75-936e-59337d0d3ba8
-- title:
--   FD: isotropic pair in lattice
-- statement:
--   The FD construction uses the isotropic pair in lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentVectorEqSmulComponent.lean#L115-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentVectorEqSmulComponent.lean#L115-L141

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankEqTwoMulHalfDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentVectorEqSmulComponent
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
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.isotropic_pair_in_lattice {r : ℕ} (X : DataX E r) {ξ x : Fin r → E} (hiso : X.IsIso ξ) (hxL : x ∈ X.L')
    (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) (hxE : ∀ e : E, x ≠ e • ξ) :
    IsIsoPair X.Gm ![ξ, (X.NC : E) • x] ∧ ∀ i, ![ξ, (X.NC : E) • x] i ∈ X.Λ := by sorry
