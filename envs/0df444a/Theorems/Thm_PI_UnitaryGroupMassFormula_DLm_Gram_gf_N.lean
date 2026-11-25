-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DLm_Gram_gf_N
-- name    : PI.UnitaryGroupMassFormula.DLm.Gram.gf_N
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:46:23.008219+00:00
-- url     : https://prove2.me/theorems/6c8f04f6-a305-5d4a-923f-a161ae2fd24e
-- title:
--   Gram: gf N
-- statement:
--   The Gram construction uses the gf N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFdGramCut.lean#L101-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFdGramCut.lean#L101-L111

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFramesCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFdGramCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DLm PI.UnitaryGroupMassFormula.DLm.Gram
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem PI.UnitaryGroupMassFormula.DLm.Gram.gf_N (D : B.RealPlaceData k r Wp Wq) {g n n' : B.Mat k r} (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) :
    Gf k r D.z D.z' (n⁻¹ * g * n') = Gf k r D.z D.z' g := by sorry
