-- Prove2me | Theorems.Thm_PI_WAU_isClosed_eqA
-- name    : PI.WAU.isClosed_eqA
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:42:41.471065+00:00
-- url     : https://prove2.me/theorems/af99ff1d-9ab5-5adc-b566-5703e13895e6
-- title:
--   WAU: is Closed eq A
-- statement:
--   The WAU construction uses the is Closed eq A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/MulVecMemLf.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/MulVecMemLf.lean#L31-L35

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_LamAfLeOhatL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_MulVecMemLf
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
open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] {B : Type} [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

theorem PI.WAU.isClosed_eqA [TopologicalSpace B] [IsTopologicalRing B] [T2Space B] {X : Type*} [TopologicalSpace X]
    {f g : X → E ⊗[F] B} (hf : CtsA b f) (hg : CtsA b g) : IsClosed {p | f p = g p} := by sorry
