-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_exists_adapted_first_projection
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.exists_adapted_first_projection
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:41:21.993342+00:00
-- url     : https://prove2.me/theorems/094d876e-1b32-4a8b-b9ae-df72cf59a7bf
-- title:
--   Sc Xu Exists: exists adapted first projection
-- statement:
--   The Sc Xu Exists construction uses the exists adapted first projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SplitGen.lean#L13-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SplitGen.lean#L13-L93

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SplitGen
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
open scoped TensorProduct
open PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso
variable {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]

theorem PI.UnitaryGroupMassFormula.ScXuExists.exists_adapted_first_projection (σ : E →ₐ[F] E) (hσσ : ∀ a, σ (σ a) = a)
    (hfix : ∀ a, σ a = a → a ∈ (algebraMap F E).range) (h2 : Module.finrank F E = 2)
    (h2K : (2 : K) ≠ 0) (ε : K ⊗[F] E) (hsum : ε + sigT σ ε = 1) (horth : ε * sigT σ ε = 0) :
    ∃ p1 : K ⊗[F] E →+* K, (∀ c : K, p1 (algebraMap K (K ⊗[F] E) c) = c) ∧ p1 ε = 1 ∧
      p1 (sigT σ ε) = 0 ∧
      ∀ r : K ⊗[F] E, r = algebraMap K (K ⊗[F] E) (p1 r) * ε +
        algebraMap K (K ⊗[F] E) (p1 (sigT σ r)) * sigT σ ε := by sorry
