-- Prove2me | Theorems.Thm_UpperTheory_V_Alg_Lift_map_hom
-- name    : UpperTheory.V.Alg.Lift.map_hom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:21.866017+00:00
-- url     : https://prove2.me/theorems/246cea9f-bd60-4395-9058-d761fde4a857
-- title:
--   Lift: map hom
-- statement:
--   The Lift construction uses the map hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/ResMapBijective.lean#L294-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/ResMapBijective.lean#L294-L295

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebra_ResMapBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open UpperTheory UpperTheory.V UpperTheory.V.Alg
attribute [instance] IsCO.complete IsCO.isLocalHom
attribute [instance] WPres.fin
variable (O : Type) [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι]
  [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O))
variable {O rbar} {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']

theorem UpperTheory.V.Alg.Lift.map_hom (f : R →ₐ[O] R') (r : Lift O rbar R) (g : Γ) (a b : ι) :
    (r.map f).hom g a b = f (r.hom g a b) := by sorry

attribute [defeq] UpperTheory.V.Alg.Lift.map_hom
