-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Cj_Bf_lin
-- name    : PI.VolSemiDirect.W.Cj.Bf_lin
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:36:16.258941+00:00
-- url     : https://prove2.me/theorems/539ac7ee-8a67-461d-b225-6e5b7208ed5e
-- title:
--   Cj: Bf lin
-- statement:
--   The Cj construction uses the Bf lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianDatumFormEq.lean#L84-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianDatumFormEq.lean#L84-L105

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_NnrealEqOneOfMulSelf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_LocallyCompactAdelicUnitary
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianDatumFormEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MeasureTheory Measure
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {A : Type} [CommRing A] [Algebra F A]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem PI.VolSemiDirect.W.Cj.Bf_lin (g : HA A σ J) (u v : Fin M → A ⊗[F] E) :
    Bf σ J (lin A σ J g u) (lin A σ J g v) = Bf σ J u v := by sorry
