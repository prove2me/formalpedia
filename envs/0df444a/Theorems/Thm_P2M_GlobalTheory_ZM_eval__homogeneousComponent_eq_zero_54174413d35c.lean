-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ZM_eval__homogeneousComponent_eq_zero_54174413d35c
-- name    : P2M_GlobalTheory_ZM_eval__homogeneousComponent_eq_zero_54174413d35c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:50:58.547877+00:00
-- url     : https://prove2.me/theorems/356f1a83-5863-491e-ba7d-47e6dc7868c9
-- title:
--   P2 M Global Theory ZM eval  homogeneous Component eq zero 54174413d35c: P2 M Global Theory ZM eval  homogeneous Component eq zero 54174413d35c
-- statement:
--   The P2 M Global Theory ZM eval  homogeneous Component eq zero 54174413d35c construction uses the P2 M Global Theory ZM eval  homogeneous Component eq zero 54174413d35c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SpMapCompRingHomComp.lean#L38-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SpMapCompRingHomComp.lean#L38-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SpMapCompRingHomComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM

theorem P2M_GlobalTheory_ZM_eval__homogeneousComponent_eq_zero_54174413d35c {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R') (w : σ → R')
    (F : MvPolynomial σ R) (e : ℕ)
    (h : MvPolynomial.eval₂Hom ((LaurentPolynomial.C : R' →+* LaurentPolynomial R').comp β)
      (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (w i)) F = 0) :
    MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) = 0 := by sorry

alias «GlobalTheory».«ZM».«eval₂_homogeneousComponent_eq_zero» := P2M_GlobalTheory_ZM_eval__homogeneousComponent_eq_zero_54174413d35c
