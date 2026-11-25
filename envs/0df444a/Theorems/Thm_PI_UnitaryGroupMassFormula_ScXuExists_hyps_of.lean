-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_hyps_of
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.hyps_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:40:45.949964+00:00
-- url     : https://prove2.me/theorems/90d90630-0e9c-4acb-ad61-8fa1c64bc655
-- title:
--   Sc Xu Exists: hyps of
-- statement:
--   The Sc Xu Exists construction uses the hyps of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/Development.lean#L60-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/Development.lean#L60-L74

import Definitions.Def_Formalism_PeriodIntegrals_ScXuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Development
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
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

theorem PI.UnitaryGroupMassFormula.ScXuExists.hyps_of {I : AutInst} {g r k : ℕ} {e f : Fin r → Fin I.n → I.E} {z : Fin I.n → I.E}
    (h1 : 1 ≤ g)
    (hs : ∀ v : HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      Nat.card {w : HeightOneSpectrum (𝓞 I.E) //
        w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} = 2)
    (hn : I.n = 2 * r + k + 1)
    (hee : ∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0)
    (hff : ∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0)
    (hef : ∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0)
    (hz : ∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (e a) z = 0 ∧
      Formalism.UG.hform (starRingEnd I.E) I.J (f a) z = 0)
    (ht : ∃ t : ℕ, t ≡ 1 [MOD g] ∧ Formalism.UG.hform (starRingEnd I.E) I.J z z = -(t : I.E))
    (hi : ∀ a, InAt I g 1 (incl I (e a)) ∧ InAt I g 1 (incl I (f a)))
    (hiz : InAt I g 1 (incl I z)) : Hyps I g r k e f z := by sorry
