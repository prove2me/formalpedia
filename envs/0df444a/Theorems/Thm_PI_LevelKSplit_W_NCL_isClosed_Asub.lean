-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCL_isClosed_Asub
-- name    : PI.LevelKSplit.W.NCL.isClosed_Asub
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:34:16.032446+00:00
-- url     : https://prove2.me/theorems/efe7735a-05d5-4102-8517-9cdd6f938b1c
-- title:
--   NCL: is Closed Asub
-- statement:
--   The NCL construction uses the is Closed Asub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/IsClosedAsub.lean#L33-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/IsClosedAsub.lean#L33-L58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LeviInfUnipotentEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCIface
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_IsClosedAsub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCL
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ}

theorem PI.LevelKSplit.W.NCL.isClosed_Asub (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) (P : Frame E M r) (T : F)
    (hP : P.IsStd σ J T) : IsClosed (Asub (Af F) σ J P : Set (HA (Af F) σ J)) := by sorry
