-- Prove2me | Theorems.Thm_PI_Dv_TIW_idx_map
-- name    : PI.Dv.TIW.idx_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:58.945491+00:00
-- url     : https://prove2.me/theorems/b498694b-66fe-47b8-815e-593233cf2af8
-- title:
--   TIW: idx map
-- statement:
--   The TIW construction uses the idx map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxNonnegOfLe.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxNonnegOfLe.lean#L43-L50

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.TIW.idx_map (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {V' : Type} [AddCommGroup V'] [Module K V']
    [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (φ : V →ₗ[K] V') (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (hker : M ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = N ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K)) :
    idxAt w M N = idxAt w (M.map (φ.restrictScalars (𝓞 K))) (N.map (φ.restrictScalars (𝓞 K))) := by sorry
