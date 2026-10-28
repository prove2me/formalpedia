-- Prove2me | Theorems.Thm_TaoFivePrimes_lemma43
-- name    : TaoFivePrimes.lemma43
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T17:06:46.157229+00:00
-- url     : https://prove2.me/theorems/2998223b-d671-40d6-b643-ddf43928a677
-- title:
--   Tao Lemma 4.3 — both zero-frequency bounds with the prime-counting input discharged
-- statement:
--   Let $x\ge1$ be real, $q\ge1$ be an integer, and let $\eta:\mathbb R\to\mathbb R$ be a bounded nonnegative function supported in $[0,1]$. Put $M=\sup_{t\in\mathbb R}|\eta(t)|$, using the pointwise supremum. Then
--
--   $$|S_{\eta,q}(x,0)|\le M\psi(x)\le1.04Mx.$$
--
--   Moreover, if $0<c\le1$, $\eta$ is smooth and supported in $[c,1]$, and $cx\ge10^8$, then
--
--   $$\left|S_{\eta,1}(x,0)-x\int_{\mathbb R}|\eta(t)|\,dt\right|\le\frac{x}{40\log(cx)}\int_{\mathbb R}|\eta'(t)|\,dt.$$
--
--   The absolute values on the complex sums are Lean's complex norm. This gives both (4.3) and (4.4) of Tao's Lemma 4.3, with the slightly stronger closed threshold. Unlike the earlier Abel summation interface, this statement does not assume a bound for $\psi$; that input is discharged by the separately proved unconditional Chebyshev estimate. The finite-sum domination, Rosser–Schoenfeld upper bound, and Abel summation proofs are reused from existing proved platform theorems.
-- source:
--   https://arxiv.org/pdf/1201.6656v4#page=16

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

open MeasureTheory

theorem TaoFivePrimes.lemma43
    (eta : ℝ → ℝ) (q : ℕ) (x : ℝ) (hq : 1 ≤ q) (hx : 1 ≤ x)
    (hnonneg : ∀ t : ℝ, 0 ≤ eta t)
    (hbounded : BddAbove (Set.range (fun t : ℝ => |eta t|)))
    (hsupp : ∀ t : ℝ, t < 0 ∨ 1 < t → eta t = 0) :
    (‖TaoFivePrimes.smoothedExpSum eta q x 0‖ ≤
        sSup (Set.range (fun t : ℝ => |eta t|)) * Chebyshev.psi x ∧
      sSup (Set.range (fun t : ℝ => |eta t|)) * Chebyshev.psi x ≤
        1.04 * sSup (Set.range (fun t : ℝ => |eta t|)) * x) ∧
    (∀ c : ℝ, 0 < c → c ≤ 1 → ContDiff ℝ (⊤ : ℕ∞) eta →
      (∀ t : ℝ, t < c ∨ 1 < t → eta t = 0) → (10 : ℝ) ^ 8 ≤ c * x →
      ‖TaoFivePrimes.smoothedExpSum eta 1 x 0 -
        (((∫ t : ℝ, |eta t|) * x : ℝ) : ℂ)‖ ≤
        1 / (40 * Real.log (c * x)) * (∫ t : ℝ, |deriv eta t|) * x) := by sorry
