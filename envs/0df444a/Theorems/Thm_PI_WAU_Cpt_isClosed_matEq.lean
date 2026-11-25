-- Prove2me | Theorems.Thm_PI_WAU_Cpt_isClosed_matEq
-- name    : PI.WAU.Cpt.isClosed_matEq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:37.411426+00:00
-- url     : https://prove2.me/theorems/5e58c7a4-0ecc-5824-bb6f-c53f44c0a547
-- title:
--   Cpt: is Closed mat Eq
-- statement:
--   The Cpt construction uses the is Closed mat Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/IsCompactCset.lean#L51-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/IsCompactCset.lean#L51-L57

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_MulVecMemLf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_IsCompactCset
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

theorem PI.WAU.Cpt.isClosed_matEq {f g : Co I × Co I → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hf : ∀ i j, CtsA (bs I) (fun p => f p i j)) (hg : ∀ i j, CtsA (bs I) (fun p => g p i j)) :
    IsClosed {p | f p = g p} := by sorry
