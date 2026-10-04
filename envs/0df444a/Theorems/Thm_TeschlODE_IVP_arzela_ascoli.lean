-- Prove2me | Theorems.Thm_TeschlODE_IVP_arzela_ascoli
-- name    : TeschlODE.IVP.arzela_ascoli
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:53:10.356393+00:00
-- url     : https://prove2.me/theorems/c4ef8f2b-c596-4db3-ab67-e8dfa7f400e6
-- title:
--   Theorem 2.18 (Arzelà–Ascoli) — bounded equicontinuous sequences in C([a,b], ℝⁿ)
-- statement:
--   Let $I = [a, b]$ be a compact interval and $x_m \in C(I, \mathbb{R}^n)$, $m \in \mathbb{N}$, a sequence that is (uniformly) **equicontinuous**: for every $\varepsilon > 0$ there is $\delta > 0$, independent of $m$, with
--   $$|x_m(t) - x_m(s)| \le \varepsilon \quad \text{if } |t - s| < \delta,\ t, s \in I,\ m \in \mathbb{N}. \qquad (2.70)$$
--   If the sequence is bounded, i.e. $\sup_m \sup_{t \in I} |x_m(t)| < \infty$, then there is a subsequence $x_{m_k}$ that converges uniformly on $I$.
--
--   In the book this is the compactness tool for the Peano existence theorem: the Euler polygons form a bounded equicontinuous family.
--
--   **Formalization Note.** Functions are $\mathbb{R} \to \mathbb{R}^n$, continuous on $[a, b]$, and only their values on $[a, b]$ matter. "Bounded" is boundedness in the sup norm (2.3) of $C(I, \mathbb{R}^n)$, i.e. one bound $R$ for all $m$ and all $t \in I$. The subsequence is given by a strictly increasing $\varphi : \mathbb{N} \to \mathbb{N}$, and uniform convergence is on $[a,b]$ to some limit function (which is then automatically continuous there). If $a > b$ the interval is empty and the statement is trivial.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 55, Theorem 2.18

import Mathlib

namespace TeschlODE.IVP

theorem arzela_ascoli {n : ℕ} (a b : ℝ) (x : ℕ → ℝ → EuclideanSpace ℝ (Fin n))
    (hcont : ∀ m : ℕ, ContinuousOn (x m) (Set.Icc a b))
    (hequi : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℕ, ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc a b,
      |t - s| < δ → ‖x m t - x m s‖ ≤ ε)
    (hbdd : ∃ R : ℝ, ∀ m : ℕ, ∀ t ∈ Set.Icc a b, ‖x m t‖ ≤ R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℝ → EuclideanSpace ℝ (Fin n),
      TendstoUniformlyOn (fun k => x (φ k)) y Filter.atTop (Set.Icc a b) := by sorry

end TeschlODE.IVP
