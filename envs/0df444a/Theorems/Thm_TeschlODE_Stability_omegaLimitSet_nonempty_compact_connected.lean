-- Prove2me | Theorems.Thm_TeschlODE_Stability_omegaLimitSet_nonempty_compact_connected
-- name    : TeschlODE.Stability.omegaLimitSet_nonempty_compact_connected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T13:29:41.448252+00:00
-- url     : https://prove2.me/theorems/5c2ffb6f-94fd-424c-8a57-7ac0b4fc857c
-- title:
--   Lemma 6.6 — $\omega_\sigma(x)$ is nonempty, compact and connected when $\gamma_\sigma(x)$ lies in a compact set
-- statement:
--   Let $M \subseteq \mathbb{R}^n$ be open, $f \in C^1(M, \mathbb{R}^n)$, and $\Phi$ the flow with maximal intervals $I_x$. Let $\sigma \in \{+1, -1\}$ and $x \in M$. If $\gamma_\sigma(x)$ is contained in a compact set $C \subseteq M$, then
--   $$\omega_\sigma(x) \ \text{ is nonempty, compact, and connected.}$$
--
--   **Formalization Note.** The book writes "a compact set $C$"; its proof starts with Lemma 6.3, which needs $C \subseteq M$, so $C \subseteq M$ is part of the hypothesis (a compact set reaching $\partial M$ allows orbits that leave $M$ in finite time, with empty $\omega_\sigma(x)$). Mathlib's `IsConnected` already includes nonemptiness; nonemptiness is also stated separately.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 194, Lemma 6.6

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsMaximalFlow
import Definitions.Def_TeschlODE_Stability_semiOrbit
import Definitions.Def_TeschlODE_Stability_omegaLimitSet

namespace TeschlODE.Stability

theorem omegaLimitSet_nonempty_compact_connected {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsCompact C) (hCM : C ⊆ M)
    (horb : semiOrbit σ I Φ x ⊆ C) :
    (omegaLimitSet M σ I Φ x).Nonempty ∧ IsCompact (omegaLimitSet M σ I Φ x) ∧
      IsConnected (omegaLimitSet M σ I Φ x) := by sorry

end TeschlODE.Stability
