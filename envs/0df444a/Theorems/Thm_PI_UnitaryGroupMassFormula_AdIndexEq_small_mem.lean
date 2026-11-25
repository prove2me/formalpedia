-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_small_mem
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.small_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:45:48.068826+00:00
-- url     : https://prove2.me/theorems/a73746ce-8549-5989-8914-62d607800562
-- title:
--   Ad Index Eq: small mem
-- statement:
--   The Ad Index Eq construction uses the small mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertPow.lean#L191-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertPow.lean#L191-L208

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.small_mem (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v)
    (P : Matrix (Fin I.n) (Fin I.n) (Av I v)) (N : ℕ)
    (h1 : ∀ z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      N • (P *ᵥ z) ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)))
    (h2 : ∀ z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      N • ((α • P) *ᵥ z) ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)))
    {w : Av I v} (hw : InR I v α w) (z : Fin I.n → Av I v)
    (hz : z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    (incL I v N * w) • (P *ᵥ z) ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by sorry
