-- Prove2me | Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity_aeval_isWH__16e475c86f62
-- name    : P2M_Formalism_GM_DimensionMonotonicity_aeval_isWH__16e475c86f62
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:57:40.982728+00:00
-- url     : https://prove2.me/theorems/14c50c01-787e-40f6-a65b-6030fab4c3c5
-- title:
--   P2 M Formalism GM Dimension Monotonicity aeval is WH  16e475c86f62: P2 M Formalism GM Dimension Monotonicity aeval is WH  16e475c86f62
-- statement:
--   The P2 M Formalism GM Dimension Monotonicity aeval is WH  16e475c86f62 construction uses the P2 M Formalism GM Dimension Monotonicity aeval is WH  16e475c86f62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1790-L1802
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1790-L1802

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M

theorem P2M_Formalism_GM_DimensionMonotonicity_aeval_isWH__16e475c86f62 {σ τ R M : Type} [CommSemiring R] [AddCommMonoid M] (w' : σ → M) (w : τ → M)
    (g : σ → MvPolynomial τ R) (hg : ∀ x, IsWeightedHomogeneous w (g x) (w' x))
    {f : MvPolynomial σ R} {d : M} (hf : IsWeightedHomogeneous w' f d) :
    IsWeightedHomogeneous w (aeval g f) d := by sorry

alias «Formalism».«GM».«DimensionMonotonicity».«aeval_isWH'» := P2M_Formalism_GM_DimensionMonotonicity_aeval_isWH__16e475c86f62
