-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_fromSpecStalk_comp_subscheme__chartPullback_eq_edf95e69c754
-- name    : P2M_FunctorialResolution_EmbeddedResolution_fromSpecStalk_comp_subscheme__chartPullback_eq_edf95e69c754
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:21.770249+00:00
-- url     : https://prove2.me/theorems/2c1de23b-284b-4ddb-9e9d-0661f20da52a
-- title:
--   P2 M Functorial Resolution Embedded Resolution from Spec Stalk comp subscheme  chart Pullback eq edf95e69c754: P2 M Functorial Resolution Embedded Resolution from Spec Stalk comp subscheme  chart Pull
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution from Spec Stalk comp subscheme  chart Pullback eq edf95e69c754 construction uses the P2 M Functorial Resolution Embedded Resolution from Spec Stalk comp subscheme  chart Pullback eq edf95e69c754 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/MaxContactChartUniqueness.lean#L710-L762
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/MaxContactChartUniqueness.lean#L710-L762

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartFiberProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafSmoothPullback
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_StalkIdealSpreadOut
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactChartUniqueness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem P2M_FunctorialResolution_EmbeddedResolution_fromSpecStalk_comp_subscheme__chartPullback_eq_edf95e69c754
    (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) {m : ℕ} (_hm : 1 ≤ m)
    (_hinv : IsMaxContactInvariant k p I m)
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (c₁ c₂ : EtaleChart p U n) (j : Fin n)
    (hcoord : ∀ i : Fin n, i ≠ j → c₁.coord i = c₂.coord i)
    (x : X) (hx : x ∈ U)
    (hmem₁ : c₁.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩)
    (hmem₂ : c₂.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩)
    (hg₁ : (X.presheaf.germ U x hx).hom (c₁.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    (hg₂ : (X.presheaf.germ U x hx).hom (c₂.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    (_hsupp : x ∈ (maxContactIdeal k p I m).support)
    [IsLocallyNoetherian (chartPullback c₁ c₂)]
    [IsLocallyNoetherian ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subscheme]
    (h : ChartsAgreeAt c₁ c₂ x hx)
    (z : ↥(((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subscheme))
    (hz : ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι.base z =
      chartPullbackPoint c₁ c₂ x hx h) :
    (((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subscheme).fromSpecStalk z ≫
        ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ≫
          chartPullbackFst c₁ c₂ =
      (((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subscheme).fromSpecStalk z ≫
        ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ≫
          chartPullbackSnd c₁ c₂ := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«fromSpecStalk_comp_subschemeι_chartPullback_eq» := P2M_FunctorialResolution_EmbeddedResolution_fromSpecStalk_comp_subscheme__chartPullback_eq_edf95e69c754
