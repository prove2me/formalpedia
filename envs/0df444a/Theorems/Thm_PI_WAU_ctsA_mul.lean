-- Prove2me | Theorems.Thm_PI_WAU_ctsA_mul
-- name    : PI.WAU.ctsA_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:56:10.660084+00:00
-- url     : https://prove2.me/theorems/0c64d7eb-eeed-4aef-b6a5-c4e7849d4e0b
-- title:
--   WAU: cts A mul
-- statement:
--   The WAU construction uses the cts A mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/CoordTmulOneMul.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/CoordTmulOneMul.lean#L94-L98

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open scoped TensorProduct
variable {F E B : Type} [Field F] [Field E] [Algebra F E] [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
variable [TopologicalSpace B] [IsTopologicalRing B]
variable {b}
variable {X : Type*} [TopologicalSpace X]

theorem PI.WAU.ctsA_mul {f g : X → E ⊗[F] B} (hf : CtsA b f) (hg : CtsA b g) : CtsA b (fun x => f x * g x) := by sorry
