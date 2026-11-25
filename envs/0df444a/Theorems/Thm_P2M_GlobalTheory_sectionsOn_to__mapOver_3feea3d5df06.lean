-- Prove2me | Theorems.Thm_P2M_GlobalTheory_sectionsOn_to__mapOver_3feea3d5df06
-- name    : P2M_GlobalTheory_sectionsOn_to__mapOver_3feea3d5df06
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:13:55.771255+00:00
-- url     : https://prove2.me/theorems/e16bc810-fad3-4d34-b1c1-916d92020b14
-- title:
--   P2 M Global Theory sections On to  map Over 3feea3d5df06: P2 M Global Theory sections On to  map Over 3feea3d5df06
-- statement:
--   The P2 M Global Theory sections On to  map Over 3feea3d5df06 construction uses the P2 M Global Theory sections On to  map Over 3feea3d5df06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsPowMulPowEqOfIsZeroCechH.lean#L461-L463
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsPowMulPowEqOfIsZeroCechH.lean#L461-L463

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe t v u
noncomputable section
open GlobalTheory
variable {X Y : Scheme.{u}} {ι : Type}
variable (g : Y ⟶ X) (V : X.Opens) (U : ι → X.Opens)
variable {R : Type v} [CommRing R] [Algebra R Γ(X, ⊤)] {S : Type t} [CommRing S]
  [Algebra S Γ(Y, ⊤)] {σ : R →+* S}
  {g} (hσ : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
  {F : X.Modules} {G : Y.Modules} (φ : F ⟶ (Scheme.Modules.pushforward g).obj G)

theorem P2M_GlobalTheory_sectionsOn_to__mapOver_3feea3d5df06 (W : X.Opens) (x : sectionsOn F W) :
    sectionsOn.toΓ G (g ⁻¹ᵁ W) (sectionsOn.mapOver hσ φ W x) = φ.app W (sectionsOn.toΓ F W x) := by sorry

alias «GlobalTheory».«sectionsOn».«toΓ_mapOver» := P2M_GlobalTheory_sectionsOn_to__mapOver_3feea3d5df06
