-- Prove2me | Theorems.Thm_TeschlODE_IVP_gronwall_generalized
-- name    : TeschlODE.IVP.gronwall_generalized
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:51:54.172899+00:00
-- url     : https://prove2.me/theorems/9e0ab9c6-1ad0-4139-b3cb-9c4eb0920f13
-- title:
--   Lemma 2.7 (Generalized Gronwall's inequality) — (2.35) and (2.36)
-- statement:
--   Let $T \in \mathbb{R}$ and let $\psi, \alpha, \beta$ be real functions continuous on $[0, T]$, with $\beta \ge 0$ there, such that
--   $$\psi(t) \le \alpha(t) + \int_0^t \beta(s)\psi(s)\,ds, \qquad t \in [0, T]. \qquad (2.34)$$
--   Then
--   $$\psi(t) \le \alpha(t) + \int_0^t \alpha(s)\beta(s) \exp\Bigl(\int_s^t \beta(r)\,dr\Bigr) ds, \qquad t \in [0, T]. \qquad (2.35)$$
--   Moreover, if in addition $\alpha(s) \le \alpha(t)$ for $0 \le s \le t \le T$, then
--   $$\psi(t) \le \alpha(t) \exp\Bigl(\int_0^t \beta(s)\,ds\Bigr), \qquad t \in [0, T]. \qquad (2.36)$$
--
--   Note that $\alpha$ may take any real values, not only nonnegative ones. The lemma is the tool behind the continuous dependence estimate of Theorem 2.8 and the global existence Theorem 2.17.
--
--   **Formalization Note.** The book leaves the regularity of $\psi$, $\alpha$, $\beta$ implicit; its proof integrates them. The statement adds continuity of all three on $[0, T]$, which makes every integral a Riemann integral of a continuous function (without integrability, a Lean integral would silently be $0$). The integrals are interval integrals $\int_0^t$, $\int_s^t$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 42, Lemma 2.7

import Mathlib

namespace TeschlODE.IVP

theorem gronwall_generalized (ψ α β : ℝ → ℝ) (T : ℝ)
    (hψ : ContinuousOn ψ (Set.Icc 0 T)) (hα : ContinuousOn α (Set.Icc 0 T))
    (hβ : ContinuousOn β (Set.Icc 0 T)) (hβ0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ β t)
    (h : ∀ t ∈ Set.Icc 0 T, ψ t ≤ α t + ∫ s in (0 : ℝ)..t, β s * ψ s) :
    (∀ t ∈ Set.Icc 0 T,
      ψ t ≤ α t + ∫ s in (0 : ℝ)..t, α s * β s * Real.exp (∫ r in s..t, β r)) ∧
    ((∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, s ≤ t → α s ≤ α t) →
      ∀ t ∈ Set.Icc 0 T, ψ t ≤ α t * Real.exp (∫ s in (0 : ℝ)..t, β s)) := by sorry

end TeschlODE.IVP
