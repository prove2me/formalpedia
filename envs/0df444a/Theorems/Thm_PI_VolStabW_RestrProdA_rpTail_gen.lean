-- Prove2me | Theorems.Thm_PI_VolStabW_RestrProdA_rpTail_gen
-- name    : PI.VolStabW.RestrProdA.rpTail_gen
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:44:54.710238+00:00
-- url     : https://prove2.me/theorems/ef62b180-44a2-41f4-b7fb-61bc114e49e6
-- title:
--   Restr Prod A: rp Tail gen
-- statement:
--   The Restr Prod A construction uses the rp Tail gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/RestrProdA.lean#L36-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/RestrProdA.lean#L36-L90

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.RestrProdA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem PI.VolStabW.RestrProdA.rpTail_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {a M d : ℕ} (b : Module.Basis (Fin d) F E)
    (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E))
    (hSB : ∀ v (Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φ → Integrable Φ (m v))
    (hmult : ∀ (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv → Multipliable (fun v => ∫ X, Φv v X ∂(m v))) :
    (∃ v, ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φ → ∫ X, Φ X ∂(m v) = 0) ∨
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ c : ENNReal, c ≠ ⊤ ∧
      HasProd (fun v : {v // v ∉ S} => m v.1 (latV b v.1)) c := by sorry
