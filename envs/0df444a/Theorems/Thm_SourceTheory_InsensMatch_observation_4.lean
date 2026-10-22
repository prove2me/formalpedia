-- Prove2me | Theorems.Thm_SourceTheory_InsensMatch_observation_4
-- name    : SourceTheory.InsensMatch.observation_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:08.90454+00:00
-- url     : https://prove2.me/theorems/c7d2a2e2-3bb0-4048-91e4-8f11b65ebc26
-- title:
--   Observation 4, p. 8775 — φ(P_A(A)) = P_C(C) iff A ~ C, > iff A ≻ C, < iff A ≺ C
-- statement:
--   Assume structural Assumption 1 and Assumption 2 for sources $\mathcal C$ and $\mathcal A$, and let $\varphi$ be a transformation with $w_{\mathcal A} = w_{\mathcal C} \circ \varphi$ on $[0,1]$ (the pmatcher from $\mathcal A$ to $\mathcal C$). Then for every $A \in \mathcal A$ and $C \in \mathcal C$:
--   1. $\varphi(P_{\mathcal A}(A)) = P_{\mathcal C}(C)$ if and only if $A \sim C$, i.e. $W(A) = W(C)$;
--   2. $\varphi(P_{\mathcal A}(A)) > P_{\mathcal C}(C)$ if and only if $A \succ C$, i.e. $W(A) > W(C)$;
--   3. $\varphi(P_{\mathcal A}(A)) < P_{\mathcal C}(C)$ if and only if $A \prec C$, i.e. $W(A) < W(C)$.
--
--   $$\varphi(P_{\mathcal A}(A)) \gtreqless P_{\mathcal C}(C) \iff W(A) \gtreqless W(C).$$
--
--   The pmatcher thus translates comparisons of events across sources into comparisons of probabilities, which is how the preference conditions of Definitions 2 and 4 become conditions on $\varphi$.
--
--   **Formalization Note.** Event preference is $W$-order (Assumption 1: events are ranked via bets on them, maximizing $W$).
-- source:
--   Baillon et al. (2025), Management Science 71(10), Observation 4, p. 8775

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.InsensMatch

open Set

/-- Observation 4 (p. 8775): for the pmatcher `φ` from `𝒜` to `𝒞`, `φ(P_𝒜(A)) = P_𝒞(C)` iff
`A ~ C`, `φ(P_𝒜(A)) > P_𝒞(C)` iff `A ≻ C`, and `φ(P_𝒜(A)) < P_𝒞(C)` iff `A ≺ C`. -/
theorem observation_4 {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : SourceTheory.Uniform.Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (h𝒞 : SourceTheory.Uniform.IsSource 𝓔 W 𝒞)
    (PC PA : Set S → ℝ) (wC wA : ℝ → ℝ) (h2 : SourceTheory.Uniform.Assumption2 pref U W 𝒞 𝒜 PC PA wC wA)
    (φ : ℝ → ℝ) (hφ : SourceTheory.Uniform.IsTransformation φ) (hφA : ∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p)) :
    ∀ A ∈ 𝒜, ∀ C ∈ 𝒞, (φ (PA A) = PC C ↔ W A = W C) ∧ (PC C < φ (PA A) ↔ W C < W A) ∧
      (φ (PA A) < PC C ↔ W A < W C) := by sorry

end SourceTheory.InsensMatch
