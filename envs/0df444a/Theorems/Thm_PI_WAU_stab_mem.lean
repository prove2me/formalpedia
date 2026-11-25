-- Prove2me | Theorems.Thm_PI_WAU_stab_mem
-- name    : PI.WAU.stab_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:46:06.036276+00:00
-- url     : https://prove2.me/theorems/b93d7216-7f4b-4157-a44d-a8bb774cdde7
-- title:
--   WAU: stab mem
-- statement:
--   The WAU construction uses the stab mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/MulVecMemLf.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/MulVecMemLf.lean#L39-L40

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

theorem PI.WAU.stab_mem {I : AutInst} {x : I.Gf} (hx : x ∈ I.Kset) {w : Fin I.n → I.E ⊗[I.F] Af I.F}
    (hw : w ∈ I.Lf) : I.fmat x *ᵥ w ∈ I.Lf := by sorry
