-- Prove2me | Theorems.Thm_QZeroSum19_GK_lemma_1
-- name    : QZeroSum19.GK.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:13.312316+00:00
-- url     : https://prove2.me/theorems/5f250d1f-bf8b-4bce-96a3-71702d779d49
-- title:
--   Lemma 1, p. 3 — with η = ε/4, after ⌈16 ln(nm/δ)/ε²⌉ iterations Algorithm 1's normalized iterates are ε-optimal with probability ≥ 1 − δ
-- statement:
--   Let $n,m\ge1$ and let $A\in[-1,1]^{n\times m}$ be the payoff matrix of a zero-sum game with value $v^*$. Let $\delta\in(0,1/3)$ and $\varepsilon\in(0,1)$, and run Algorithm 1 (Grigoriadis–Khachiyan sampling play) with the fixed step $\eta=\varepsilon/4$. Put
--   $$T=\Big\lceil\frac{16\ln(nm/\delta)}{\varepsilon^2}\Big\rceil .$$
--   Then for every $t\ge T$, with probability at least $1-\delta$, the normalized iterates $x_t/\|x_t\|_1$ and $y_t/\|y_t\|_1$ after $t$ iterations are $\varepsilon$-optimal strategies:
--   $$A^{\mathsf T}\frac{x_t}{\|x_t\|_1}\ \ge\ (v^*-\varepsilon)e,\qquad A\frac{y_t}{\|y_t\|_1}\ \le\ (v^*+\varepsilon)e .$$
--
--   This is the classical convergence guarantee on which the paper's quantum algorithms (Theorems 9 and 11) are built: they implement the same iteration with a faster Gibbs sampler.
--
--   **Formalization Note** The probability is that of the sample-path law of Algorithm 1 defined in the definition file. "After $T$ iterations" is stated for every iteration count $t\ge T$, each separately, which includes $t=T$. Since $nm/\delta>3$, $T\ge1$, so the iterates are nonzero and their normalization is a probability vector.
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 3, Lemma 1, second sentence (proof pp. 4–5)

import Mathlib
import Definitions.Def_QZeroSum19_GK_Setting

open Matrix

namespace QZeroSum19.GK

/-- **Lemma 1** (p. 3), fixed accuracy-goal version: for `δ ∈ (0, 1/3)` and `ε ∈ (0, 1)`,
running Algorithm 1 with `η = ε/4`, with probability at least `1 − δ` the normalized iterates
`x/‖x‖₁` and `y/‖y‖₁` are `ε`-optimal after `T = ⌈16 ln(nm/δ)/ε²⌉` iterations (stated at every
`t ≥ T`). -/
theorem lemma_1 {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) (δ ε : ℝ) (hδ : 0 < δ) (hδ3 : δ < 1 / 3) (hε : 0 < ε)
    (hε1 : ε < 1) (t : ℕ) (ht : ⌈16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2⌉₊ ≤ t) :
    1 - δ ≤ prob A (etaFixed ε) t (fun ω =>
      IsEpsOptimalAlice A ε (normalize (xAfter (etaFixed ε) ω t)) ∧
      IsEpsOptimalBob A ε (normalize (yAfter (etaFixed ε) ω t))) := by sorry

end QZeroSum19.GK
