-- Prove2me | Theorems.Thm_PI_VolStabW_RestrProdA_repr_change
-- name    : PI.VolStabW.RestrProdA.repr_change
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:40:03.233847+00:00
-- url     : https://prove2.me/theorems/e83dc82d-6c59-55a5-9112-0e4186156a65
-- title:
--   Restr Prod A: repr change
-- statement:
--   The Restr Prod A construction uses the repr change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/RestrProdA.lean#L92-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/RestrProdA.lean#L92-L112

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.RestrProdA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem PI.VolStabW.RestrProdA.repr_change {F E : Type} [Field F] [Field E] [Algebra F E] {d d' : ℕ}
    (R : Type) [CommRing R] [Algebra F R] (b : Module.Basis (Fin d) F E)
    (b' : Module.Basis (Fin d') F E) (y : R ⊗[F] E) (k' : Fin d') :
    (Algebra.TensorProduct.basis R b').repr y k' =
      ∑ k, (Algebra.TensorProduct.basis R b).repr y k * algebraMap F R (b'.repr (b k) k') := by sorry
