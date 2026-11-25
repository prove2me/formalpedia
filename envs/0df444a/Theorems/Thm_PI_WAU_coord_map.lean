-- Prove2me | Theorems.Thm_PI_WAU_coord_map
-- name    : PI.WAU.coord_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:44:01.036507+00:00
-- url     : https://prove2.me/theorems/5229c05f-25b6-4e22-9c5a-9a27083cf47b
-- title:
--   WAU: coord map
-- statement:
--   The WAU construction uses the coord map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/CoordTmulOneMul.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/CoordTmulOneMul.lean#L60-L66

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

theorem PI.WAU.coord_map (σ : E →ₐ[F] E) (x : E ⊗[F] B) :
    coord b (Algebra.TensorProduct.map σ (AlgHom.id F B) x) =
      fun k => ∑ i, b.repr (σ (b i)) k • coord b x i := by sorry
