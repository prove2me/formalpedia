-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_linOf_basis
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.linOf_basis
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:48.02505+00:00
-- url     : https://prove2.me/theorems/bf83b641-932f-43fe-b33b-d487e5a6b972
-- title:
--   UJClass Mass: lin Of basis
-- statement:
--   The UJClass Mass construction uses the lin Of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/EquivFunLinOf.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/EquivFunLinOf.lean#L67-L72

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem PI.UnitaryGroupMassFormula.UJClassMass.linOf_basis {M : ℕ} (b : Module.Basis (Fin M) E V) (u : GL (Fin M) E) (i : Fin M) :
    linOf b u (b i) = ∑ k, (u : Matrix (Fin M) (Fin M) E) k i • b k := by sorry
