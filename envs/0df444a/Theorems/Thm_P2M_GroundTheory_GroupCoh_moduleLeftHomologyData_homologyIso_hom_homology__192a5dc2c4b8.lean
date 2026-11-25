-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_moduleLeftHomologyData_homologyIso_hom_homology__192a5dc2c4b8
-- name    : P2M_GroundTheory_GroupCoh_moduleLeftHomologyData_homologyIso_hom_homology__192a5dc2c4b8
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:30.874291+00:00
-- url     : https://prove2.me/theorems/8b396ab6-1a07-4a2c-aac7-13c4541d4de1
-- title:
--   P2 M Ground Theory Group Coh module Left Homology Data homology Iso hom homology  192a5dc2c4b8: P2 M Ground Theory Group Coh module Left Homology Data homology Iso hom homology  192a5dc2c4b8
-- statement:
--   The P2 M Ground Theory Group Coh module Left Homology Data homology Iso hom homology  192a5dc2c4b8 construction uses the P2 M Ground Theory Group Coh module Left Homology Data homology Iso hom homology  192a5dc2c4b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ModuleHomologyData.lean#L78-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ModuleHomologyData.lean#L78-L91

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ModuleHomologyData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits
universe u
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (ModuleCat.{u} R))
    (K : Type u) [AddCommGroup K] [Module R K] (ι : K →ₗ[R] S.X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker S.g.hom) (N : Submodule R K)
    (hN : ∀ x, x ∈ N ↔ ι x ∈ LinearMap.range S.f.hom)

theorem P2M_GroundTheory_GroupCoh_moduleLeftHomologyData_homologyIso_hom_homology__192a5dc2c4b8 [S.HasHomology]
    (z : S.cycles) (x : K) (hx : ι x = S.iCycles.hom z) :
    (moduleLeftHomologyData S K ι hι hrange N hN).homologyIso.hom.hom (S.homologyπ.hom z) =
      Submodule.Quotient.mk x := by sorry

alias «GroundTheory».«GroupCoh».«moduleLeftHomologyData_homologyIso_hom_homologyπ» := P2M_GroundTheory_GroupCoh_moduleLeftHomologyData_homologyIso_hom_homology__192a5dc2c4b8
