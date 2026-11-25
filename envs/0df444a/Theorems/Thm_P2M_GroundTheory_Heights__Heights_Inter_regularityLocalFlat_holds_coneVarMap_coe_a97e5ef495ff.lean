-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_coe_a97e5ef495ff
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_coe_a97e5ef495ff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:59.053548+00:00
-- url     : https://prove2.me/theorems/01439507-19f2-480f-9d53-1e1d61e4a58c
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds cone Var Map coe a97e5ef495ff: P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds cone Var Map coe a97e5ef495ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds cone Var Map coe a97e5ef495ff construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds cone Var Map coe a97e5ef495ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L52-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L52-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsLocalizationConeVarMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_coe_a97e5ef495ff (hPW : P ≤ W) (v : ∀ k, ι k) (G : MvPolynomial K (locRing P W)) :
    ((coneVarMap P W hPW v G : coneLocRing P W hPW) : FractionRing (MRing ι ⧸ P)) =
      ∑ e ∈ G.support, ((coeff e G : locRing P W) : FractionRing (MRing ι ⧸ P)) * fracHom P (varMono v e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalFlat_holds».«coneVarMap_coe» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_coe_a97e5ef495ff
