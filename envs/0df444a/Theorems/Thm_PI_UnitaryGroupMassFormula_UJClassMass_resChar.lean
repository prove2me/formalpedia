-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_resChar
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.resChar
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:04:36.92993+00:00
-- url     : https://prove2.me/theorems/6667f9e7-558d-4683-9ed2-c43f3034aee7
-- title:
--   UJClass Mass: res Char
-- statement:
--   The UJClass Mass construction uses the res Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/LSLocA.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/LSLocA.lean#L11-L25

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_SigRTmulOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSLocA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped TensorProduct ComplexOrder
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass

theorem PI.UnitaryGroupMassFormula.UJClassMass.resChar {E : Type} [Field E] [NumberField E] (P : Ideal (𝓞 E)) (hP : P.IsMaximal) :
    ∃ p : ℕ, p.Prime ∧ ∀ m : ℕ, ¬ p ∣ m → (m : 𝓞 E) ∉ P := by sorry
