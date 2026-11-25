-- Prove2me | Theorems.Thm_PI_MSC_nablaSpan_eq
-- name    : PI.MSC.nablaSpan_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:36.744553+00:00
-- url     : https://prove2.me/theorems/48626760-9f4e-5211-af73-6f4e5b45db3f
-- title:
--   MSC: nabla Span eq
-- statement:
--   The MSC construction uses the nabla Span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/RenameInitMinor.lean#L47-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/RenameInitMinor.lean#L47-L57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MinorSpanCompl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ExistsCoeffNeZeroOfMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ShapeColumnDegreeColumnSizes
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_RenameInitMinor
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.MSC

theorem PI.MSC.nablaSpan_eq (R : Type) [CommRing R] (N : ℕ) (ν : YoungDiagram) :
    PI.nablaSpan R N ν = Submodule.map (rename (phi N (ν.colLen 0))).toLinearMap
      (Submodule.span R (Set.range (gen R N ν))) := by sorry
