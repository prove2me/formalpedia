-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_coordMonomial_563e18c6b1cf
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_coordMonomial_563e18c6b1cf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:25:36.580955+00:00
-- url     : https://prove2.me/theorems/d63495f7-ccab-4397-a8a0-f836bf325f78
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IUnique is Multi Homog coord Monomial 563e18c6b1cf: P2 M Ground Theory Heights  Heights Inter Thm IUnique is Multi Homog coord Monomial 563e18c6b1cf
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IUnique is Multi Homog coord Monomial 563e18c6b1cf construction uses the P2 M Ground Theory Heights  Heights Inter Thm IUnique is Multi Homog coord Monomial 563e18c6b1cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIUnique.lean#L65-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmIUnique.lean#L65-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmIUnique
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIUnique
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_coordMonomial_563e18c6b1cf (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIUnique».«isMultiHomog_coordMonomial» := P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_coordMonomial_563e18c6b1cf
