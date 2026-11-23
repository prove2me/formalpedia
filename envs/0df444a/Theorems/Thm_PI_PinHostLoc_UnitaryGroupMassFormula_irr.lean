-- Prove2me | Theorems.Thm_PI_PinHostLoc_UnitaryGroupMassFormula_irr
-- name    : PI.PinHostLoc.UnitaryGroupMassFormula.irr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:36:43.308676+00:00
-- url     : https://prove2.me/theorems/1e65c3cc-67df-4452-a7f5-06a62f439494
-- title:
--   Unitary Group Mass Formula: irr
-- statement:
--   The Unitary Group Mass Formula construction uses the irr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalResidueCharacter/ResCharEq.lean#L56-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalResidueCharacter/ResCharEq.lean#L56-L110

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PinHostLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalResidueCharacter_ResCharEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField ValuativeRel WithZero
open PI PI.PinHostLoc PI.PinHostLoc.UnitaryGroupMassFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : Formalism.MainNotions.S.Loc.LocAt F E sig p)

theorem PI.PinHostLoc.UnitaryGroupMassFormula.irr {g : ℕ} (hg0 : g ≠ 0) (hin : ((g : ℕ) : 𝓞 F) ∈ p.asIdeal)
    (hnot : ((g : ℕ) : 𝓞 F) ∉ p.asIdeal ^ 2) : Irreducible ((g : ℕ) : 𝒪[A.Fp]) := by sorry
