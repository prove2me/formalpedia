-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_forget__homologyMap_comp_forget_HomologyIso_83a1bdaab274
-- name    : P2M_GroundTheory_ProfCoh_forget__homologyMap_comp_forget_HomologyIso_83a1bdaab274
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:54:35.666803+00:00
-- url     : https://prove2.me/theorems/612366f5-f507-4559-a581-c7fa25f76f74
-- title:
--   P2 M Ground Theory Prof Coh forget  homology Map comp forget Homology Iso 83a1bdaab274: P2 M Ground Theory Prof Coh forget  homology Map comp forget Homology Iso 83a1bdaab274
-- statement:
--   The P2 M Ground Theory Prof Coh forget  homology Map comp forget Homology Iso 83a1bdaab274 construction uses the P2 M Ground Theory Prof Coh forget  homology Map comp forget Homology Iso 83a1bdaab274 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalClassFormation/FiniteVanishing/IntScalars.lean#L59-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalClassFormation/FiniteVanishing/IntScalars.lean#L59-L83

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalClassFormation_FiniteVanishing_IntScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Limits groupCohomology
variable {Γ : Type} [Group Γ]

theorem P2M_GroundTheory_ProfCoh_forget__homologyMap_comp_forget_HomologyIso_83a1bdaab274
    {S₁ T₁ : ShortComplex (ModuleCat.{0} (ULift.{0} ℤ))} {S₂ T₂ : ShortComplex (ModuleCat.{0} ℤ)}
    (φ₁ : S₁ ⟶ T₁) (φ₂ : S₂ ⟶ T₂)
    (σS : (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).mapShortComplex.obj S₁ ≅
      (forget₂ (ModuleCat.{0} ℤ) Ab).mapShortComplex.obj S₂)
    (σT : (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).mapShortComplex.obj T₁ ≅
      (forget₂ (ModuleCat.{0} ℤ) Ab).mapShortComplex.obj T₂)
    (h : (forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).mapShortComplex.map φ₁ ≫ σT.hom =
      σS.hom ≫ (forget₂ (ModuleCat.{0} ℤ) Ab).mapShortComplex.map φ₂) :
    (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{0} (ULift.{0} ℤ)) Ab).map φ₁ ≫
        (forget₂HomologyIso σT).hom =
      (forget₂HomologyIso σS).hom ≫
        (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{0} ℤ) Ab).map φ₂ := by sorry

alias «GroundTheory».«ProfCoh».«forget₂_homologyMap_comp_forget₂HomologyIso» := P2M_GroundTheory_ProfCoh_forget__homologyMap_comp_forget_HomologyIso_83a1bdaab274
