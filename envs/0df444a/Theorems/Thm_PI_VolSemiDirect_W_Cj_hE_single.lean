-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Cj_hE_single
-- name    : PI.VolSemiDirect.W.Cj.hE_single
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:58:42.768231+00:00
-- url     : https://prove2.me/theorems/8530162d-1142-48df-ae75-5698821e0e31
-- title:
--   Cj: h E single
-- statement:
--   The Cj construction uses the h E single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/TraceGramNondegenerate.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/TraceGramNondegenerate.lean#L66-L69

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjHA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_TraceGramNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

theorem PI.VolSemiDirect.W.Cj.hE_single {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x : Fin M → E) (j : Fin M) (c : E) :
    hE σ J x (Pi.single j c) = (∑ i, σ (x i) * J i j) * c := by sorry
