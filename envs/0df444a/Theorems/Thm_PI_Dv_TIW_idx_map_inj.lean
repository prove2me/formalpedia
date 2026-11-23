-- Prove2me | Theorems.Thm_PI_Dv_TIW_idx_map_inj
-- name    : PI.Dv.TIW.idx_map_inj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:48.649459+00:00
-- url     : https://prove2.me/theorems/0be60cd9-35d9-4a1f-8654-2c2dddb3f5d6
-- title:
--   TIW: idx map inj
-- statement:
--   The TIW construction uses the idx map inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxNonnegOfLe.lean#L52-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxNonnegOfLe.lean#L52-L64

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

theorem PI.Dv.TIW.idx_map_inj (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {V' : Type} [AddCommGroup V'] [Module K V']
    [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (φ : V →ₗ[K] V') (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (hinjM : ∀ x ∈ M, φ x = 0 → x = 0) (hinjN : ∀ x ∈ N, φ x = 0 → x = 0) :
    idxAt w M N = idxAt w (M.map (φ.restrictScalars (𝓞 K))) (N.map (φ.restrictScalars (𝓞 K))) := by sorry
