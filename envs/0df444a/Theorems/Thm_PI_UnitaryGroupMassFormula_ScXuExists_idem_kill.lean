-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_idem_kill
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.idem_kill
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:42:53.091472+00:00
-- url     : https://prove2.me/theorems/ba5eebe7-946b-400b-9bd6-36baba381b32
-- title:
--   Sc Xu Exists: idem kill
-- statement:
--   The Sc Xu Exists construction uses the idem kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LocalIdempotentExistence.lean#L19-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LocalIdempotentExistence.lean#L19-L43

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_NatCastTmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocalIdempotentExistence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

theorem PI.UnitaryGroupMassFormula.ScXuExists.idem_kill (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (g : ℕ) (hg : (g : 𝓞 I.F) ∈ v.asIdeal)
    (c : RV I v) (hcc : c * c = c)
    (hc : ∀ x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      ∃ w ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), c • x = (g : RV I v) • w) :
    ∀ x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), c • x = 0 := by sorry
