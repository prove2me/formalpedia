-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_ZuckToRaw_dsigW_zero__89af3ac8d530
-- name    : P2M_GlobalTheory_CompanionTheory_ZuckToRaw_dsigW_zero__89af3ac8d530
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:04:04.546376+00:00
-- url     : https://prove2.me/theorems/7df96cd9-3ac6-41ae-85c1-25dbab33c0f4
-- title:
--   P2 M Global Theory Companion Theory Zuck To Raw dsig W zero  89af3ac8d530: P2 M Global Theory Companion Theory Zuck To Raw dsig W zero  89af3ac8d530
-- statement:
--   The P2 M Global Theory Companion Theory Zuck To Raw dsig W zero  89af3ac8d530 construction uses the P2 M Global Theory Companion Theory Zuck To Raw dsig W zero  89af3ac8d530 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ToRawComplex.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ToRawComplex.lean#L14-L21

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ToRawComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckToRaw
variable {k r : ℕ}

theorem P2M_GlobalTheory_CompanionTheory_ZuckToRaw_dsigW_zero__89af3ac8d530 (R : Rep k r) (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :
    PI.UpqRep.dsigW (k := k) (r := r) R.σ W (0 : R.H) = 0 := by sorry

alias «GlobalTheory».«CompanionTheory».«ZuckToRaw».«dsigW_zero'» := P2M_GlobalTheory_CompanionTheory_ZuckToRaw_dsigW_zero__89af3ac8d530
