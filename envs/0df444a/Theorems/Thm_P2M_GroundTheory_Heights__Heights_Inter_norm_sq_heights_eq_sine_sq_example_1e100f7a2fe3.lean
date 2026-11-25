-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_norm_sq_heights_eq_sine_sq_example_1e100f7a2fe3
-- name    : P2M_GroundTheory_Heights__Heights_Inter_norm_sq_heights_eq_sine_sq_example_1e100f7a2fe3
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:24:44.250817+00:00
-- url     : https://prove2.me/theorems/223c9cee-4de2-4af5-a2ef-4a73b1a27fa5
-- title:
--   P2 M Ground Theory Heights  Heights Inter norm sq heights eq sine sq example 1e100f7a2fe3: P2 M Ground Theory Heights  Heights Inter norm sq heights eq sine sq example 1e100f7a2fe3
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter norm sq heights eq sine sq example 1e100f7a2fe3 construction uses the P2 M Ground Theory Heights  Heights Inter norm sq heights eq sine sq example 1e100f7a2fe3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L719-L754
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L719-L754

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_TsgPolyVolPolyCoeffEven
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
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
open MvPolynomial Matrix ComplexOrder ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
attribute [instance] ProjectiveLineBundle.fieldΩ ProjectiveLineBundle.finι ProjectiveLineBundle.finν ProjectiveLineBundle.finκ ProjectiveLineBundle.acgE ProjectiveLineBundle.modE
  ProjectiveLineBundle.fieldΦ ProjectiveLineBundle.algΦ

theorem P2M_GroundTheory_Heights__Heights_Inter_norm_sq_heights_eq_sine_sq_example_1e100f7a2fe3 (z : (Σ k, ExW k) → ℂ) (hblk : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ‖eval z (map (Int.castRingHom ℂ) exg)‖ ^ 2 * exXi.h (fun p => z (T.yyEmb 0 p)) *
        exXi.h (fun p => z (T.yyEmb 1 p)) =
      ‖eval z (map (Int.castRingHom ℂ) exh)‖ ^ 2 *
        sinSqG (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) (fun k : Unit ⊕ Unit => z ⟨.line0, k⟩)
          (fun k : Unit ⊕ Unit => z ⟨.line1, k⟩) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«norm_sq_heights_eq_sine_sq_example» := P2M_GroundTheory_Heights__Heights_Inter_norm_sq_heights_eq_sine_sq_example_1e100f7a2fe3
