-- Prove2me | Theorems.Thm_PI_Dv_TIW_idx_smulSub_map
-- name    : PI.Dv.TIW.idx_smulSub_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:51.215332+00:00
-- url     : https://prove2.me/theorems/18c60f4e-ce3d-420e-be38-d43d9741825e
-- title:
--   TIW: idx smul Sub map
-- statement:
--   The TIW construction uses the idx smul Sub map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxSmulSubMap.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxSmulSubMap.lean#L76-L83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
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

theorem PI.Dv.TIW.idx_smulSub_map (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (d : K) (hd : d ≠ 0)
    (M N : Submodule (𝓞 K) V) (hM : M.FG) (hN : N.FG)
    (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V)) :
    idxAt w (smulSub d M) (smulSub d N) = idxAt w M N := by sorry
