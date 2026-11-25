-- Prove2me | Theorems.Thm_PI_NglqJacSplitW_image_update_pi
-- name    : PI.NglqJacSplitW.image_update_pi
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:35:18.977961+00:00
-- url     : https://prove2.me/theorems/45526bd2-ac52-4560-854c-914b0e4570c5
-- title:
--   Nglq Jac Split W: image update pi
-- statement:
--   The Nglq Jac Split W construction uses the image update pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/DiagonalOneJacobian.lean#L40-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/DiagonalOneJacobian.lean#L40-L67

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiscreteHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiagonalOneJacobian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Function Topology
open scoped ENNReal NNReal Pointwise
open PI PI.NglqJacSplitW
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem PI.NglqJacSplitW.image_update_pi (i : ι) (a : F) (_ha : a ≠ 0) (s : ι → Set F) :
    (fun x => update x i (a * x i)) '' (univ.pi s) =
      univ.pi (update s i ((fun y => a * y) '' s i)) := by sorry
