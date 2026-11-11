-- Prove2me | Theorems.Thm_PriceIgnorance_Pairwise_lemma_C_4
-- name    : PriceIgnorance.Pairwise.lemma_C_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:13:12.629752+00:00
-- url     : https://prove2.me/theorems/ac7938fd-5ddc-41a7-9750-2316efbd891f
-- title:
--   Lemma C.4 — balls and squares: if $K=\omega(n^3\log C)$ and $C=\omega(1)$ then $\mathbb P[G]=1-o(1)$
-- statement:
--   There are $C$ colors, each with $K$ disjoint triples of balls, and $n$ squares; all $3CK+n$ objects arrive in uniformly random order. Let $G$ be the event that at least one complete triple of every color arrives before any square. If $K=\omega(n^3\log C)$ and $C=\omega(1)$, then $\mathbb P[G]=1-o(1)$. Explicitly: for any sequences $(C_j,K_j,n_j)_{j\ge0}$ of natural numbers with
--   $$C_j\to\infty\qquad\text{and}\qquad\frac{K_j}{n_j^3\log C_j}\to\infty,$$
--   one has
--   $$\mathbb P[G_j]\to1\qquad(j\to\infty),$$
--   where $G_j$ is the event $G$ for $C_j$ colors, $K_j$ triples per color and $n_j$ squares.
--
--   This is the probabilistic step of Theorem 3.19: with enough masked triples, a correlation-aware algorithm decodes every hidden sample before any value of interest arrives.
--
--   Differences from the source:
--   - encoding: K = ω(n³ log C), C = ω(1), P[G] = 1 − o(1) → for sequences (C_j, K_j, n_j): C_j → ∞ and K_j / (n_j³ log C_j) → ∞ imply P[G_j] → 1; reason: the standard meaning of the asymptotic notation, all three parameters varying
--   - encoding: the ratio K/(n³ log C) → real division, with x/0 = 0 in Lean; reason: a sequence whose denominator vanishes infinitely often (n_j = 0 or C_j = 1) has no ratio tending to ∞, so it is excluded; there ω(n³ log C) is undefined
--   - encoding: objects arriving in uniformly random order → a uniformly random bijection from the 3CK + n objects to the positions 0..3CK + n − 1; P[G] = #G / #bijections; reason: same distribution of the arrival order
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 30, Lemma C.4 (proof p. 31)

import Mathlib
import Definitions.Def_PriceIgnorance_Pairwise_BallsSquares

open Filter Topology

namespace PriceIgnorance.Pairwise

/-- Lemma C.4 (p. 30), balls and squares, with explicit asymptotics: along any sequence of
parameters `(C_j, K_j, n_j)` with `C_j → ∞` (`C = ω(1)`) and `K_j / (n_j³ log C_j) → ∞`
(`K = ω(n³ log C)`), the probability that every color has a complete triple arriving before every
square tends to `1` (`P[G] = 1 − o(1)`). -/
theorem lemma_C_4 (C K n : ℕ → ℕ)
    (hC : Tendsto (fun j => (C j : ℝ)) atTop atTop)
    (hK : Tendsto (fun j => (K j : ℝ) / ((n j : ℝ) ^ 3 * Real.log (C j))) atTop atTop) :
    Tendsto (fun j => probG (C j) (K j) (n j)) atTop (𝓝 1) := by sorry

end PriceIgnorance.Pairwise
