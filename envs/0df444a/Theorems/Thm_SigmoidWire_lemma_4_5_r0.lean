-- Prove2me | Theorems.Thm_SigmoidWire_lemma_4_5_r0
-- name    : SigmoidWire.lemma_4_5_r0
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:05:39.69678+00:00
-- url     : https://prove2.me/theorems/a7426156-b980-49b2-83c4-8cf7ce1a724e
-- title:
--   Proof of Lemma 4.5: $r_0=1/(1+T_k)$ approximates Sigmoid on $(-\infty,L+1]$
-- statement:
--   Let $L\ge0$ be real, let $k\ge10(L+1)$ be an odd integer, and let $T_k(y)=\sum_{j=0}^{k-1}(-y)^j/j!$ be the Taylor polynomial of $e^{-y}$. Then:
--
--   1. for every $y\in[-(L+1),L+1]$,
--   $$|T_k(y)-e^{-y}|\le e^{L+1}\,\frac{(L+1)^k}{(k/e)^k},$$
--   and this bound is at most $e^{L+1}(e/10)^{10(L+1)}\le e^{-L+1}$;
--   2. $x\mapsto 1/(1+x)$ is $1$-Lipschitz on $[0,\infty)$;
--   3. $T_k(y)>0$ for all real $y$;
--   4. for $x\le-(L+1)$: $T_k(x)\ge T_k(-(L+1))\ge e^{L+1}-e^{-L+1}$, $\ 1/(1+T_k(x))\le e^{-(L+1)}$ and $\mathrm{Sigmoid}(x)\le e^{-(L+1)}$;
--   5. for every $x\le L+1$,
--   $$\Bigl|\frac1{1+T_k(x)}-\mathrm{Sigmoid}(x)\Bigr|\le e^{-L+1}.$$
--
--   This is the part of the approximation of Sigmoid that handles $x$ up to $L+1$, with a rational function without real poles.
--
--   Differences from the source:
--   - generalization: k the least odd integer with k ≥ 10(L + 1) → every odd k ≥ 10(L + 1), and every real L ≥ 0; reason: the least such k is one of these, and L = O(ln(1/ε)) of the proof is a nonnegative real
--   - reading: error η with e^{−L+1} ≤ η → error e^{−L+1}; reason: this is the bound the proof derives; η enters only through e^{−L+1} ≤ η, so any such η follows
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), proof of Lemma 4.5, p.61

import Mathlib

namespace SigmoidWire

/-- **Proof of Lemma 4.5, the Taylor step: `r₀(x) = 1/(1 + T_k(x))` approximates `Sigmoid` on
`(−∞, L + 1]`.**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), proof of Lemma 4.5, p.61
(PDF p.63). With `T_k(y) = Σ_{j=0}^{k−1} (−y)^j / j!` and `k` odd, `k ≥ 10(L + 1)`: for
`y ∈ [−(L+1), L+1]`, `|T_k(y) − e^{−y}| ≤ e^{L+1} · (L+1)^k/(k/e)^k`, and this is at most
`e^{L+1} · (e/10)^{10(L+1)} ≤ e^{−L+1}`; `x ↦ 1/(1+x)` is 1-Lipschitz over `ℝ₊`; `T_k(y) > 0` for all
`y ∈ ℝ`; for `x ≤ −(L+1)`, `T_k(x) ≥ T_k(−(L+1)) ≥ e^{L+1} − η`, `r₀(x) ≤ e^{−(L+1)}` and
`Sigmoid(x) ≤ e^{−(L+1)}`; and `r₀(x) := 1/(1 + T_k(x))` approximates `Sigmoid(x)` with error `η` for
every `x ∈ [−(L+1), L+1]` and every `x ≤ −(L+1)`.

**Formalization Note.** The paper takes `k` to be the least odd integer `≥ 10(L+1)` and some
`L = O(ln(1/ε))` with `e^{−L+1} ≤ η`. The statement is made for every real `L ≥ 0` and every odd
`k ≥ 10(L+1)`, with `e^{−L+1}` in place of `η` (any `η ≥ e^{−L+1}` then works). The approximation
claims on `[−(L+1), L+1]` and on `x ≤ −(L+1)` are stated once, for `x ≤ L + 1`. The Lagrange
remainder point `ξ` of the paper's display is not named; its bound is. Powers with real exponents
are `Real.rpow`. -/
theorem lemma_4_5_r0 (L : ℝ) (hL : 0 ≤ L) (k : ℕ) (hk : Odd k) (hkL : 10 * (L + 1) ≤ k) :
    let T : ℝ → ℝ := fun y => ∑ j ∈ Finset.range k, (-y) ^ j / (j.factorial : ℝ)
    (∀ y ∈ Set.Icc (-(L + 1)) (L + 1),
      |T y - Real.exp (-y)| ≤ Real.exp (L + 1) * ((L + 1) ^ k / ((k : ℝ) / Real.exp 1) ^ k)) ∧
    Real.exp (L + 1) * ((L + 1) ^ k / ((k : ℝ) / Real.exp 1) ^ k) ≤
      Real.exp (L + 1) * (Real.exp 1 / 10) ^ (10 * (L + 1)) ∧
    Real.exp (L + 1) * (Real.exp 1 / 10) ^ (10 * (L + 1)) ≤ Real.exp (-L + 1) ∧
    (∀ u v : ℝ, 0 ≤ u → 0 ≤ v → |1 / (1 + u) - 1 / (1 + v)| ≤ |u - v|) ∧
    (∀ y : ℝ, 0 < T y) ∧
    (∀ x : ℝ, x ≤ -(L + 1) →
      T (-(L + 1)) ≤ T x ∧ Real.exp (L + 1) - Real.exp (-L + 1) ≤ T (-(L + 1)) ∧
      1 / (1 + T x) ≤ Real.exp (-(L + 1)) ∧ Real.sigmoid x ≤ Real.exp (-(L + 1))) ∧
    ∀ x : ℝ, x ≤ L + 1 → |1 / (1 + T x) - Real.sigmoid x| ≤ Real.exp (-L + 1) := by sorry

end SigmoidWire
