-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_finMat_patch_inv
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.finMat_patch_inv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:52:20.110863+00:00
-- url     : https://prove2.me/theorems/a6b598e0-3528-5877-83f8-72d0a5e63e46
-- title:
--   UJClass Mass: fin Mat patch inv
-- statement:
--   The UJClass Mass construction uses the fin Mat patch inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjA.lean#L97-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjA.lean#L97-L106

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem PI.UnitaryGroupMassFormula.UJClassMass.finMat_patch_inv (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (hσe : ∀ i, sigR (AF F) σ (e i) = e i) (γ : ι → GL (Fin M) E)
    (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J) :
    finMat σ J (patchHA σ J e he hs hσe γ hγ)⁻¹ =
      ∑ i, finE F E (e i) • ((γ i)⁻¹ : GL (Fin M) E).val.map (inclR (Af F)) := by sorry
