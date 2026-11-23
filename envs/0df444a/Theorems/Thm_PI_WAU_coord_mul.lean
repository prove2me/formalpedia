-- Prove2me | Theorems.Thm_PI_WAU_coord_mul
-- name    : PI.WAU.coord_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:56:01.910738+00:00
-- url     : https://prove2.me/theorems/db8ffc63-ca8c-4526-ad04-a6df8e91a0c6
-- title:
--   WAU: coord mul
-- statement:
--   The WAU construction uses the coord mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/CoordTmulOneMul.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/CoordTmulOneMul.lean#L46-L51

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open scoped TensorProduct
variable {F E B : Type} [Field F] [Field E] [Algebra F E] [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

theorem PI.WAU.coord_mul (x y : E ⊗[F] B) :
    coord b (x * y) = fun k => ∑ i, ∑ j, b.repr (b i * b j) k • (coord b x i * coord b y j) := by sorry
