-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_emb_mem
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.emb_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:30.537513+00:00
-- url     : https://prove2.me/theorems/11214ae9-5dc2-46a2-b31d-eaf79234f657
-- title:
--   UJClass Fin: emb mem
-- statement:
--   The UJClass Fin construction uses the emb mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/Development.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/Development.lean#L41-L43

import Definitions.Def_Formalism_PeriodIntegrals_UJClassFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem PI.UnitaryGroupMassFormula.UJClassFin.emb_mem (g : UJ (σ : E →+* E) J) : emb σ J g ∈ GamG σ J := by sorry
