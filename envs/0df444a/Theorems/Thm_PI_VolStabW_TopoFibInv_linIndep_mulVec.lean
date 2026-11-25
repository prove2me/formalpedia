-- Prove2me | Theorems.Thm_PI_VolStabW_TopoFibInv_linIndep_mulVec
-- name    : PI.VolStabW.TopoFibInv.linIndep_mulVec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:46:18.219622+00:00
-- url     : https://prove2.me/theorems/270dc806-41da-5c2f-92d3-7e2ba1a3ee77
-- title:
--   Topo Fib Inv: lin Indep mul Vec
-- statement:
--   The Topo Fib Inv construction uses the lin Indep mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TopoFibInv.lean#L72-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TopoFibInv.lean#L72-L89

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PullLocSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoFibInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.TopoFibInv
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem PI.VolStabW.TopoFibInv.linIndep_mulVec {A : Type} [CommRing A] (G : GL (Fin M) A) (X : Fin a → Fin M → A) :
    LinearIndependent A (fun x => (G : Matrix (Fin M) (Fin M) A) *ᵥ X x) ↔ LinearIndependent A X := by sorry
