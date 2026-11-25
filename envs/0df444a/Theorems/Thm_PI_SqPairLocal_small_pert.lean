-- Prove2me | Theorems.Thm_PI_SqPairLocal_small_pert
-- name    : PI.SqPairLocal.small_pert
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:25:13.721811+00:00
-- url     : https://prove2.me/theorems/d8150363-9d3e-588b-87ca-70cc792dcedf
-- title:
--   Sq Pair Local: small pert
-- statement:
--   The Sq Pair Local construction uses the small pert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L160-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L160-L181

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
variable {Q : Ideal (𝓞 E)} [Q.IsPrime] {c : 𝓞 E} {L : Submodule (𝓞 E) (Fin N → E)}

theorem PI.SqPairLocal.small_pert (hL : IsSDG E N L) {e₀ D : Matrix (Fin N) (Fin N) E} {ρ : 𝓞 E}
    (h₀ : Pres L e₀) (hD : Pres L D) (hρ : Dv Q c ρ) (hρc : Dv Q c (cj E ρ))
    (g1 : SmallAt Q c L (e₀ * e₀ - e₀)) (g2 : SmallAt Q c L (e₀ + e₀ᴴ - 1)) :
    SmallAt Q c L ((e₀ + (ρ : E) • D) * (e₀ + (ρ : E) • D) - (e₀ + (ρ : E) • D)) ∧
      SmallAt Q c L ((e₀ + (ρ : E) • D) + (e₀ + (ρ : E) • D)ᴴ - 1) := by sorry
