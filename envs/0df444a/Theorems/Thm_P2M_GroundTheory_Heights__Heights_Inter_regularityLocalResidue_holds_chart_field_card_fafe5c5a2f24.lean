-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_chart_field_card_fafe5c5a2f24
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_chart_field_card_fafe5c5a2f24
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:32.983094+00:00
-- url     : https://prove2.me/theorems/b382254c-8de5-4ed9-879b-15b1206fc5b4
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds chart field card fafe5c5a2f24: P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds chart field card fafe5c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds chart field card fafe5c5a2f24 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Residue holds chart field card fafe5c5a2f24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L72-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean#L72-L125

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_chart_field_card_fafe5c5a2f24 {W : Ideal (MRing ι)} [W.IsPrime] (hWmh : IsMultiHomogIdeal W) {T : ∀ k, ι k}
    (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι) ∉ W)
    (hdim : ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞))
    (p : ℕ) [Fact p.Prime] (hp : (C (p : ℤ) : MRing ι) ∈ W) :
    IsField (MRing ι ⧸ (W ⊔ Ideal.span (Set.range fun k => (X ⟨k, T k⟩ : MRing ι) - 1))) ∧
      Finite (MRing ι ⧸ (W ⊔ Ideal.span (Set.range fun k => (X ⟨k, T k⟩ : MRing ι) - 1))) ∧
      Nat.card (MRing ι ⧸ (W ⊔ Ideal.span (Set.range fun k => (X ⟨k, T k⟩ : MRing ι) - 1))) =
        p ^ (Module.length ℤ (MRing ι ⧸ (W ⊔ Ideal.span (Set.range fun k => (X ⟨k, T k⟩ : MRing ι) - 1)))).toNat := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalResidue_holds».«chart_field_card» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_chart_field_card_fafe5c5a2f24
