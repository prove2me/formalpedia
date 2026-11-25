-- Prove2me | Theorems.Thm_PI_Dv_TIW_idx_matV
-- name    : PI.Dv.TIW.idx_matV
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:32:44.181305+00:00
-- url     : https://prove2.me/theorems/cb829c35-fff5-5d03-9ff3-e1dcdffb1fcf
-- title:
--   TIW: idx mat V
-- statement:
--   The TIW construction uses the idx mat V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MatVTransvection.lean#L79-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MatVTransvection.lean#L79-L171

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
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

theorem PI.Dv.TIW.idx_matV (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {n : Type} [Fintype n] [DecidableEq n]
    (M : Submodule (𝓞 K) V) (hM : M.FG) (A : Matrix n n K) (hA : A.det ≠ 0) :
    idxAt w (latPow n M) ((latPow n M).map ((matV A).restrictScalars (𝓞 K))) =
      (Formalism.HN.rkK M : ℤ) * vAdd w A.det := by sorry
