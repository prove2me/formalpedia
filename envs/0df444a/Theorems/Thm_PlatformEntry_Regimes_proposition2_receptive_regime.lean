-- Prove2me | Theorems.Thm_PlatformEntry_Regimes_proposition2_receptive_regime
-- name    : PlatformEntry.Regimes.proposition2_receptive_regime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:52.27836+00:00
-- url     : https://prove2.me/theorems/e30b5f0b-ba43-40db-ac2e-7384cd7026ad
-- title:
--   Proposition 2, PDF p. 16 — the seller prefers entry iff (δ,f,β) ∈ Ω; Ω is an upper set in δ and in f and the complement of a band in β
-- statement:
--   Let $H$ be given by (8) and $\Omega = \{(\delta,f,\beta) \mid H > 1/4\}$, and let $\Pi^S_N(e_S)$ and $\Pi^S_E(e_S)$ be the seller's two-stage profits (6) and (7) under non-entry and under entry. Then:
--
--   1. for all $\delta\in[0,1]$, $f\in[0,1)$, $\beta\in[0,1]$, every $c_S$, $a$ and every effort $e_S$ with $a + e_S \ne 0$, the seller prefers the platform's entry to non-entry if and only if $(\delta,f,\beta) \in \Omega$:
--   $$\Pi^S_E(e_S) > \Pi^S_N(e_S) \iff (\delta,f,\beta) \in \Omega;$$
--   2. for every $f\in[0,1)$ and $\beta\in[0,1]$ there is a threshold $\tilde\delta(f,\beta)$ such that, for $\delta \in [0,1]$, $(\delta,f,\beta)\in\Omega \iff \delta > \tilde\delta(f,\beta)$;
--   3. for every $\delta\in[0,1]$ and $\beta\in[0,1]$ there is a threshold $\tilde f(\delta,\beta)$ such that, for $f \in [0,1)$, $(\delta,f,\beta)\in\Omega \iff f > \tilde f(\delta,\beta)$;
--   4. for every $\delta\in[0,1]$ and $f\in[0,1)$ there are thresholds $\beta_1(\delta,f) \le \beta_2(\delta,f)$ such that, for $\beta \in [0,1]$, $(\delta,f,\beta)\in\Omega \iff \beta < \beta_1(\delta,f)$ or $\beta > \beta_2(\delta,f)$.
--
--   $\Omega$ is the receptive regime: there the platform's spillover outweighs the added competition, and the seller should welcome rather than deter the platform's entry. The threshold structure says the regime grows with the spillover and with the referral rate, while in the competition intensity it is the complement of a band.
--
--   **Formalization Note** The paper's "for any $e_S$" is read with $a + e_S \neq 0$: at $a + e_S = 0$ both profits equal $-c_S e_S^2$ and no strict preference is possible. Condition (5) is not assumed in item 1, since $H = 0$ off (5), nor in items 2–4. The thresholds, "defined in the proof", are existentials that depend on the two fixed parameters only.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), PDF p. 16, Proposition 2 (Ω defined PDF p. 15); proof Online Supplement, Appendix A, PDF pp. 35–36

import Mathlib
import Definitions.Def_PlatformEntry_Regimes_Model

namespace PlatformEntry.Regimes

theorem proposition2_receptive_regime :
    (∀ δ f β cS a e : ℝ, InBox δ f β → a + e ≠ 0 →
      (profitN δ f β cS a e < profitE δ f β cS a e ↔ Omega δ f β)) ∧
    (∀ f β : ℝ, 0 ≤ f → f < 1 → 0 ≤ β → β ≤ 1 →
      ∃ δt : ℝ, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → (Omega δ f β ↔ δt < δ)) ∧
    (∀ δ β : ℝ, 0 ≤ δ → δ ≤ 1 → 0 ≤ β → β ≤ 1 →
      ∃ ft : ℝ, ∀ f : ℝ, 0 ≤ f → f < 1 → (Omega δ f β ↔ ft < f)) ∧
    (∀ δ f : ℝ, 0 ≤ δ → δ ≤ 1 → 0 ≤ f → f < 1 →
      ∃ β₁ β₂ : ℝ, β₁ ≤ β₂ ∧
        ∀ β : ℝ, 0 ≤ β → β ≤ 1 → (Omega δ f β ↔ β < β₁ ∨ β₂ < β)) := by sorry

end PlatformEntry.Regimes
