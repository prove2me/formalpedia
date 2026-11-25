-- Prove2me | Theorems.Thm_PI_FT_cont_sandwich
-- name    : PI.FT.cont_sandwich
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:58.000688+00:00
-- url     : https://prove2.me/theorems/2891ec96-7a91-4ae2-a63a-9d0a003cb1d3
-- title:
--   FT: cont sandwich
-- statement:
--   The FT construction uses the cont sandwich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/InstIsModTopTens.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/InstIsModTopTens.lean#L41-L47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_InstIsModTopTens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

theorem PI.FT.cont_sandwich {T : Type*} [TopologicalSpace T] {m n p q : Type*} [Fintype n] [Fintype p]
    (C : Matrix m n (R ⊗[F] E)) (D : Matrix p q (R ⊗[F] E)) {f : T → Matrix n p (R ⊗[F] E)}
    (hf : Continuous f) : Continuous (fun t => C * f t * D) := by sorry
