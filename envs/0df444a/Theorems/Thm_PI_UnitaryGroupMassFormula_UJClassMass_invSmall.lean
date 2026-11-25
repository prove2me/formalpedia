-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_invSmall
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.invSmall
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:43:09.617497+00:00
-- url     : https://prove2.me/theorems/7622a45f-61d8-4af0-9670-19b32767d999
-- title:
--   UJClass Mass: inv Small
-- statement:
--   The UJClass Mass construction uses the inv Small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/SigRTmulOne.lean#L91-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/SigRTmulOne.lean#L91-L145

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PsiInclR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_SigRTmulOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {M : ℕ}

theorem PI.UnitaryGroupMassFormula.UJClassMass.invSmall (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) {dI dJ : ℕ}
    (hdI : ∀ i j, IsIntegral ℤ ((dI : E) * J⁻¹ i j)) (hdJ : ∀ i j, IsIntegral ℤ ((dJ : E) * J i j))
    (e : Af F) (kk : HA (AF F) σ J) (N : ℕ)
    (h : ∀ i j, ∃ o ∈ Oh F E, (e ⊗ₜ[F] (1 : E)) * (finMat σ J kk⁻¹ - 1) i j = (dI * dJ * N) • o) :
    ∀ i j, ∃ o ∈ Oh F E, (e ⊗ₜ[F] (1 : E)) * (finMat σ J kk - 1) i j = N • o := by sorry
