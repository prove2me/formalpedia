-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_loc_bound
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.loc_bound
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:39:15.870491+00:00
-- url     : https://prove2.me/theorems/17a5afa5-a388-4df5-ba27-769f85892010
-- title:
--   Ad Index Eq: loc bound
-- statement:
--   The Ad Index Eq construction uses the loc bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertPow.lean#L156-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertPow.lean#L156-L170

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S

theorem PI.UnitaryGroupMassFormula.AdIndexEq.loc_bound (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (Mx : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) {N : ℕ}
    (hM : ∀ w ∈ I.Lf, N • (Mx *ᵥ w) ∈ I.Lf) (z : Fin I.n → Av I v)
    (hz : z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    N • (Mx.map (PI.FinKW.psiV I v).toRingHom *ᵥ z) ∈
      Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by sorry
