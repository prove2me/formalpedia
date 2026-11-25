-- Prove2me | Theorems.Thm_PI_ScRefExists_GWG_side_mem
-- name    : PI.ScRefExists.GWG.side_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:23:50.847807+00:00
-- url     : https://prove2.me/theorems/66706b92-c5af-5b65-a901-74a6bcb98490
-- title:
--   GWG: side mem
-- statement:
--   The GWG construction uses the side mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/GWGlue.lean#L114-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/GWGlue.lean#L114-L177

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GlobWIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GWGlue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GWG
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.ScRefExists.GWG.side_mem {r k M : ℕ} (e f : Fin r → Fin I.n → I.E) (θ : 𝓞 I.E) (G ga : ℕ) (qa qb w wab : ℤ)
    (z za zb : Fin I.n → I.E) (b ba bb bd bda bdb : Fin k → Fin I.n → I.E)
    (hza : za ∈ I.L) (hzb : zb ∈ I.L)
    (hbL : ∀ i, ba i ∈ I.L ∧ bb i ∈ I.L ∧ bda i ∈ I.L ∧ bdb i ∈ I.L)
    (hsum : (qa : I.E) + (qb : I.E) = 1) (hprod : (qa : I.E) * (qb : I.E) = (G : I.E) * (wab : I.E))
    (hga : (qa : I.E) * (ga : I.E) = (G : I.E) * (w : I.E))
    (hz : z = qa • za + qb • zb) (hb : ∀ i, b i = qa • ba i + qb • bb i)
    (hbd : ∀ i, bd i = qa • bda i + qb • bdb i) {y : Fin I.n → I.E}
    (hsp : y ∈ Submodule.span (𝓞 I.E) (SS I r k M e f θ za ba bda) ⊔ gL I ga) :
    qa • y ∈ Submodule.span (𝓞 I.E) (SS I r k M e f θ z b bd) ⊔ gL I G := by sorry
