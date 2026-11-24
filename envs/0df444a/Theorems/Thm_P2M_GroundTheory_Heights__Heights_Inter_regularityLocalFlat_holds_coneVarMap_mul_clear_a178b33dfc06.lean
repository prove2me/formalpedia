-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_mul_clear_a178b33dfc06
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_mul_clear_a178b33dfc06
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:39.179493+00:00
-- url     : https://prove2.me/theorems/eee22b60-32d1-47d4-9c83-9450ac4630b4
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds cone Var Map mul clear a178b33dfc06: P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds cone Var Map mul clear
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds cone Var Map mul clear a178b33dfc06 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds cone Var Map mul clear a178b33dfc06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L99-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L99-L108

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
variable {P W}

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_mul_clear_a178b33dfc06 (hPW : P ≤ W) (v : ∀ k, ι k) (G : MvPolynomial K (locRing P W))
    {V : MRing ι} {b : K → ℕ} {N : (K →₀ ℕ) → MRing ι}
    (hN : ∀ e, IsMultiHomog (N e) b ∧
        ((coeff e G : locRing P W) : FractionRing (MRing ι ⧸ P)) * fracHom P V = fracHom P (N e)) :
    ((coneVarMap P W hPW v G : coneLocRing P W hPW) : FractionRing (MRing ι ⧸ P)) * fracHom P V =
      fracHom P (∑ e ∈ G.support, N e * varMono v e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalFlat_holds».«coneVarMap_mul_clear» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_mul_clear_a178b33dfc06
