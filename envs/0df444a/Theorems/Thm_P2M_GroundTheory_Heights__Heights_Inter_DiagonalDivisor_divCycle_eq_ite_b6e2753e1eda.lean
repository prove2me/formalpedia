-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalDivisor_divCycle_eq_ite_b6e2753e1eda
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalDivisor_divCycle_eq_ite_b6e2753e1eda
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:37.60879+00:00
-- url     : https://prove2.me/theorems/a38dba03-08f0-4bac-a85c-4c5a28a8385e
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Divisor div Cycle eq ite b6e2753e1eda: P2 M Ground Theory Heights  Heights Inter Diagonal Divisor div Cycle eq ite b6e2753e1eda
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Divisor div Cycle eq ite b6e2753e1eda construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Divisor div Cycle eq ite b6e2753e1eda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagDiv.lean#L29-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagDiv.lean#L29-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagDiv
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalDivisor
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open Classical

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalDivisor_divCycle_eq_ite_b6e2753e1eda {P : Ideal (MRing ι)} [P.IsPrime] {s u : MRing ι} (hu : u ∉ P)
    (W : Ideal (MRing ι)) :
    divCycle P s W = if W ∈ divSupp P (s * u) then multAt (P ⊔ Ideal.span {s}) W else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalDivisor».«divCycle_eq_ite» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalDivisor_divCycle_eq_ite_b6e2753e1eda
