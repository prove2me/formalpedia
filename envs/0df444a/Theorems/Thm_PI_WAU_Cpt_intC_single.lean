-- Prove2me | Theorems.Thm_PI_WAU_Cpt_intC_single
-- name    : PI.WAU.Cpt.intC_single
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:45:33.919684+00:00
-- url     : https://prove2.me/theorems/aa442bb7-fe9c-48ea-9503-f1a0a7bfb2f1
-- title:
--   Cpt: int C single
-- statement:
--   The Cpt construction uses the int C single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/MulVecMemLf.lean#L109-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/MulVecMemLf.lean#L109-L114

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
open PI.WAU.Cpt
variable (I : AutInst)

theorem PI.WAU.Cpt.intC_single (D1 : ℕ) (h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F))) (j : Fin I.n) :
    ∀ i, IntC (bs I) ((Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F) i) := by sorry
