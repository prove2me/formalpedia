-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialGlobalSectionsEquiv_D
-- name    : QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalSectionsEquiv_D
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:59:22.168716+00:00
-- url     : https://prove2.me/theorems/800db15d-4bbf-4aca-910c-1674d5e0644d
-- title:
--   Algebraic Geometry: affine Differential Global Sections Equiv D
-- statement:
--   The Algebraic Geometry construction uses the affine Differential Global Sections Equiv D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineDifferentials.lean#L439-L450
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineDifferentials.lean#L439-L450

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeDifferentials
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) (A : CommRingCat.{u}) [CommRing k] [Algebra k A]
local notation "M" => ModuleCat.of A (KaehlerDifferential k A)
local notation "T" => tilde (R := A) M
local notation "B" => @PrimeSpectrum.basicOpen A _
local notation "F" => affineDifferentialUnderlyingRingPresheaf A
local notation "S" => affineDifferentialTildeAbelianSheaf k A
attribute [local instance] basicOpenAlgebra basicOpenLocalization basicOpenModule
  basicOpenAModule basicOpenModuleTower basicOpenBaseAlgebra basicOpenBaseTower
  basicOpenTildeLocalization basicOpenKModule basicOpenKModuleTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.affineDifferentialTildeOpenModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.affineDifferentialTildeBasicModule
local notation "cA" => affineDifferentialGlobalConstantMap k A
local notation "Omegap" => schemeDifferentialPresheaf (Spec A) (CommRingCat.of k) cA
local notation "Omega" => schemeDifferentialSheaf (Spec A) (CommRingCat.of k) cA
local notation "phiA" => schemeConstantPresheafMap (Spec A) (CommRingCat.of k) cA
attribute [local instance] QEC.Coding.AlgebraicGeometry.affineDifferentialOmegaOpenAModule

theorem QEC.Coding.AlgebraicGeometry.affineDifferentialGlobalSectionsEquiv_D (a : A) :
    affineDifferentialGlobalSectionsEquiv k A
      ((schemeDifferentialSheafDerivation (Spec A) (CommRingCat.of k) cA).d
        ((Scheme.ΓSpecIso A).inv a)) = KaehlerDifferential.D k A a := by sorry
