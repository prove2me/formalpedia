-- Prove2me | Theorems.Thm_PI_VolStabW_RestrictedProductFiber_fib_props
-- name    : PI.VolStabW.RestrictedProductFiber.fib_props
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:45:45.142796+00:00
-- url     : https://prove2.me/theorems/68510fa4-7bf5-4866-b1d5-6311c39523d6
-- title:
--   Restricted Product Fiber: fib props
-- statement:
--   The Restricted Product Fiber construction uses the fib props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FiniteOnCompacts.lean#L45-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FiniteOnCompacts.lean#L45-L74

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FiniteOnCompacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology
open scoped TensorProduct
open PI.VolStabW.RestrictedProductFiber

theorem PI.VolStabW.RestrictedProductFiber.fib_props {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] (hTF : TensFacts F E σ M J a R)
    (T : Matrix (Fin a) (Fin a) E) (hT : ∀ i j, σ (T j i) = T i j) (hdet : T.det ≠ 0)
    (μ : Measure (Fin a → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ a))
    (fib : HermR R σ a → Measure (Fin a → Fin M → R ⊗[F] E))
    (h : IsFibreFamily μ (gramR R σ J) Subtype.val
      {X | LinearIndependent (R ⊗[F] E) X} ν Set.univ fib) :
    SigmaFinite (fib (hermOf R σ T hT)) ∧
    ∀ Φ : (Fin a → Fin M → R ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable Φ (fib (hermOf R σ T hT)) := by sorry
