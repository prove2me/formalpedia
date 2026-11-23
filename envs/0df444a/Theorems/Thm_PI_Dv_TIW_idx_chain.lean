-- Prove2me | Theorems.Thm_PI_Dv_TIW_idx_chain
-- name    : PI.Dv.TIW.idx_chain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:11.524989+00:00
-- url     : https://prove2.me/theorems/a1901859-ccce-4d39-8d60-fa1989420e2d
-- title:
--   TIW: idx chain
-- statement:
--   The TIW construction uses the idx chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxNonnegOfLe.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxNonnegOfLe.lean#L24-L28

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

theorem PI.Dv.TIW.idx_chain (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (M N P : Submodule (𝓞 K) V) (hM : M.FG) (hN : N.FG)
    (hP : P.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (h2 : Submodule.span K (P : Set V) = Submodule.span K (N : Set V)) :
    idxAt w M P = idxAt w M N + idxAt w N P := by sorry
