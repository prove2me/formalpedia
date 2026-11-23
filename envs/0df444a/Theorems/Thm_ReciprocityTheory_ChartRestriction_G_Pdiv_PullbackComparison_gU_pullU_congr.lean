-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_congr
-- name    : ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_pullU_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:44.459892+00:00
-- url     : https://prove2.me/theorems/f6383775-d524-4d07-a15c-3c7a2b5c3503
-- title:
--   Pullback Comparison: g U pull U congr
-- statement:
--   The Pullback Comparison construction uses the g U pull U congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/ExistsGenTransfer.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/ExistsGenTransfer.lean#L51-L55

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

theorem ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_pullU_congr {X Y : Scheme.{0}} {φ ψ : Y ⟶ X} (h : φ = ψ) (U : X.Opens) (x : Γ(X, U)ˣ)
    (p : Y) (hp : p ∈ φ ⁻¹ᵁ U) (hp' : p ∈ ψ ⁻¹ᵁ U) :
    gU p hp (pullU φ U x) = gU p hp' (pullU ψ U x) := by sorry
