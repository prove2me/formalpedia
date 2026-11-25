-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_sigR_epsT
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.sigR_epsT
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:45:32.972206+00:00
-- url     : https://prove2.me/theorems/43187e48-3d1d-46ca-b7d2-fab7ac50d66b
-- title:
--   UJClass Mass: sig R eps T
-- statement:
--   The UJClass Mass construction uses the sig R eps T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PPatchF.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PPatchF.lean#L39-L41

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_AlgebraMapIntIntAf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PPatchF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PI.UnitaryGroupMassFormula.UJClassMass.sigR_epsT (σ : E →ₐ[F] E) (T : Set (HeightOneSpectrum (𝓞 F))) : PI.UJClassFin.sigR (AF F) σ (epsT E T) = epsT E T := by sorry
