-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_Lam_emb_mul
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.Lam_emb_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:33.874814+00:00
-- url     : https://prove2.me/theorems/7665813b-3bc9-466e-a75b-8ec1ba7531fd
-- title:
--   UJClass Fin: Lam emb mul
-- statement:
--   The UJClass Fin construction uses the Lam emb mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/Development.lean#L60-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/Development.lean#L60-L78

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

theorem PI.UnitaryGroupMassFormula.UJClassFin.Lam_emb_mul (L : Set (Fin M → E)) (g : UJ (σ : E →+* E) J) (h : HA (AF F) σ J) :
    abelian₂ σ J L (emb σ J g * h) =
      (fun x => ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec x) '' abelian₂ σ J L h := by sorry
