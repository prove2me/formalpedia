-- Prove2me | Theorems.Thm_PI_WAU_Cpt_continuous_psi
-- name    : PI.WAU.Cpt.continuous_psi
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:44:53.897847+00:00
-- url     : https://prove2.me/theorems/b0643fa2-24c0-4dc1-863c-196390ce9d83
-- title:
--   Cpt: continuous psi
-- statement:
--   The Cpt construction uses the continuous psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/NatSmulMulEq.lean#L104-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/NatSmulMulEq.lean#L104-L166

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_IsCompactCset
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_NatSmulMulEq
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

theorem PI.WAU.Cpt.continuous_psi (N d D m : ℕ) (hd : 0 < d) (hD : 0 < D) (hm : 0 < m)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    (hup : ∀ y ∈ I.Lf, ∀ j, IntC (bs I) (D • y j))
    (hmul : ∀ x y : I.E ⊗[I.F] Af I.F, IntC (bs I) x → IntC (bs I) y → IntC (bs I) (m • (x * y))) :
    Continuous (psi I N) := by sorry
