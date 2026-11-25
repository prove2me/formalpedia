-- Prove2me | Theorems.Thm_PI_PinHostLoc_UnitaryGroupMassFormula_unit
-- name    : PI.PinHostLoc.UnitaryGroupMassFormula.unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:06.718968+00:00
-- url     : https://prove2.me/theorems/3d8f1e90-2c56-4c3c-87c6-97d703d7e094
-- title:
--   Unitary Group Mass Formula: unit
-- statement:
--   The Unitary Group Mass Formula construction uses the unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalResidueCharacter/ResCharEq.lean#L112-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalResidueCharacter/ResCharEq.lean#L112-L126

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

theorem PI.PinHostLoc.UnitaryGroupMassFormula.unit {n : ℕ} (hn : ((n : ℕ) : 𝓞 F) ∉ p.asIdeal) :
    ∃ u : 𝒪[A.Fp], IsUnit u ∧ (u : A.Fp) = A.ιF ((n : ℕ) : F) := by sorry
