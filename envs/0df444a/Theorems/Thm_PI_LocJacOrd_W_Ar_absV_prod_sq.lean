-- Prove2me | Theorems.Thm_PI_LocJacOrd_W_Ar_absV_prod_sq
-- name    : PI.LocJacOrd.W.Ar.absV_prod_sq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:49.125377+00:00
-- url     : https://prove2.me/theorems/1988f73b-0d38-453b-9f3e-aa847ed9ee44
-- title:
--   Ar: abs V prod sq
-- statement:
--   The Ar construction uses the abs V prod sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianOrder/AbsVNeZero.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianOrder/AbsVNeZero.lean#L53-L56

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_AbsVNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocJacOrd PI.LocJacOrd.W PI.LocJacOrd.W.Ar
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem PI.LocJacOrd.W.Ar.absV_prod_sq {r : ℕ} (s : Finset (Fin (r + 1))) (f : Fin (r + 1) → Fv F v) :
    absV v (∏ i ∈ s, f i ^ 2) = ∏ i ∈ s, absV v (f i) ^ 2 := by sorry
