-- Prove2me | Theorems.Thm_P2M_MainStatements_Hodge_Pf_WedgeProjections_theta__Multi_85cb7f90be53
-- name    : P2M_MainStatements_Hodge_Pf_WedgeProjections_theta__Multi_85cb7f90be53
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:12.501187+00:00
-- url     : https://prove2.me/theorems/954f4233-c843-4694-afb7-1fb4fbbeef93
-- title:
--   P2 M Main Statements Hodge Pf Wedge Projections theta  Multi 85cb7f90be53: P2 M Main Statements Hodge Pf Wedge Projections theta  Multi 85cb7f90be53
-- statement:
--   The P2 M Main Statements Hodge Pf Wedge Projections theta  Multi 85cb7f90be53 construction uses the P2 M Main Statements Hodge Pf Wedge Projections theta  Multi 85cb7f90be53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/AbelianDeRham/AbelianWedgeProducts/ThetaMulti.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/AbelianDeRham/AbelianWedgeProducts/ThetaMulti.lean#L17-L20

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianWedgeProducts_ThetaMulti
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MainStatements MainStatements.Hodge MainStatements.Hodge.Pf MainStatements.Hodge.Pf.WedgeProjections
variable {K : Type} [Field K] {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  (p q : V →ₗ[K] W) (r₁ r₂ : W →ₗ[K] V)

theorem P2M_MainStatements_Hodge_Pf_WedgeProjections_theta__Multi_85cb7f90be53 (g : Fin 2 → Module.Dual K V) (v : Fin 2 → W) :
    theta r₁ r₂ g (exteriorPower.ιMulti K 2 v) =
      g 0 (r₁ (v 0)) * g 1 (r₂ (v 1)) - g 1 (r₂ (v 0)) * g 0 (r₁ (v 1)) := by sorry

alias «MainStatements».«Hodge».«Pf».«WedgeProjections».«theta_ιMulti» := P2M_MainStatements_Hodge_Pf_WedgeProjections_theta__Multi_85cb7f90be53
