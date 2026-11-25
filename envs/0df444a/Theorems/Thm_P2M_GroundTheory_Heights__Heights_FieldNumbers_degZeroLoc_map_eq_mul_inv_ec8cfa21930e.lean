-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_map_eq_mul_inv_ec8cfa21930e
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_map_eq_mul_inv_ec8cfa21930e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:54:30.976492+00:00
-- url     : https://prove2.me/theorems/9776bff1-dab2-4066-9b72-f83c72225834
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers deg Zero Loc map eq mul inv ec8cfa21930e: P2 M Ground Theory Heights  Heights Field Numbers deg Zero Loc map eq mul inv ec8cfa21930e
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers deg Zero Loc map eq mul inv ec8cfa21930e construction uses the P2 M Ground Theory Heights  Heights Field Numbers deg Zero Loc map eq mul inv ec8cfa21930e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LocalIntegralClosureChart.lean#L111-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LocalIntegralClosureChart.lean#L111-L153

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsNoetherIntegralClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LocalIntegralClosureChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_map_eq_mul_inv_ec8cfa21930e (hQ : DegZeroLocQuot.Statement.{u})
    (hD : MChartDehomog.Statement.{u}) (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime]
    (hPW : P ≤ W) (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) {Ω : Type*} [Field Ω]
    [Algebra F Ω] (φ : FractionRing (MRing ι F ⧸ P) →ₐ[F] Ω) :
    Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))) ≤ (degZeroLoc P {W}).map φ ∧
      ∀ a ∈ (degZeroLoc P {W}).map φ,
        ∃ r ∈ Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))),
        ∃ d ∈ Algebra.adjoin F (Set.range fun v => φ (chartMap P u (X v))),
          d ≠ 0 ∧ d⁻¹ ∈ (degZeroLoc P {W}).map φ ∧ a = r * d⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«degZeroLoc_map_eq_mul_inv» := P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_map_eq_mul_inv_ec8cfa21930e
