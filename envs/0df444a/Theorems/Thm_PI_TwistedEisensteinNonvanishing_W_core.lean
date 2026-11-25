-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_core
-- name    : PI.TwistedEisensteinNonvanishing.W.core
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:37:28.784796+00:00
-- url     : https://prove2.me/theorems/3f0c2563-1bab-409b-9124-9e83588c9790
-- title:
--   W: core
-- statement:
--   The W construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/TwistedEisensteinOfHypotheses.lean#L92-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/TwistedEisensteinOfHypotheses.lean#L92-L138

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_TwistedEisensteinOfHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE

theorem PI.TwistedEisensteinNonvanishing.W.core {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E))
    (hp : (Ideal.absNorm P.asIdeal).Prime) (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    (hq0 : ((qOf P : ℕ) : K) ≠ 0) (hStab : StabP) (hCoV : CoVP) (hXX : XXP) (hTA : TrAffP)
    (hRX : ResXSurjP) (hCA : ChArgP) (hCB : ChArgBddP)
    {n' c' n c D j : ℕ} (hjD : j ≤ D) {psi : E → K} (hpsi : PsiOk D P psi)
    (G G' : SF E K (n' + c') (n + c)) (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) (hρ : ρ ∈ R1 E n c)
    (C : K) (hC : C ≠ 0) (hCeq : ∀ x, G' x = C * G (ρ.toLinearMap ∘ₗ x))
    (hS : ∀ x, G x ≠ 0 → ∀ (s : ℕ) (l : Fin (n + c)), IntAt P ((qOf P : E) ^ j * x (eN E (n' + c') s) l))
    (hS' : ∀ x, G' x ≠ 0 → ∀ (s : ℕ) (l : Fin (n + c)), IntAt P ((qOf P : E) ^ j * x (eN E (n' + c') s) l))
    (hH : ∀ y : (Fin n' → E) →ₗ[E] (Fin n → E),
      Good P j j (fun t : FC n' c' n c → E => G (xx1 y t) * psi (-chArg (xx1 y t))))
    (hne : ∃ A0 B0 : ℕ, ∀ A' B', A0 ≤ A' → B0 ≤ B' →
      (fun xj : (Fin n' → E) →ₗ[E] (Fin n → E) =>
        RS P A' B' (fun t : FC n' c' n c → E => G (xx1 xj t) * psi (-chArg (xx1 xj t)))) ≠ 0) :
    ∃ A0 B0 : ℕ, ∀ A' B', A0 ≤ A' → B0 ≤ B' →
      (fun xj : (Fin n' → E) →ₗ[E] (Fin n → E) =>
        RS P A' B' (fun t : FC n' c' n c → E => G' (xx1 xj t) * psi (-chArg (xx1 xj t)))) ≠ 0 := by sorry
