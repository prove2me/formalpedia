-- Prove2me | Theorems.Thm_StableCountSub3_lemma_5_13
-- name    : StableCountSub3.lemma_5_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:52:09.786802+00:00
-- url     : https://prove2.me/theorems/20a6b7a2-362f-48d4-8a5b-0740adc2c31e
-- title:
--   Lemma 5.13 — $e_s\le1+p_c$, $e_s\le2(1-p_c)$, $e_s\le4/3$
-- statement:
--   For every instance, $e_s\le1+p_c$, $e_s\le2(1-p_c)$ and $e_s\le\frac43$, where for $(\mu,m)$ uniform on $\Omega\times M$ and $D=D(\mu)$, $e_s$ is the probability that the backward direction is simple plus the probability that the forward direction is simple, and $p_c$ is the probability that $m\in C$ in the backward direction. At $n=0$, both quantities are defined to be zero.
--
--   Differences from the source:
--   - encoding: men M = {m1,…,mn}, women W = {w1,…,wn}, strict complete preference lists, perfect matchings as bijections M → W, the order ⪯ and the cover relation ⋖ of Definitions 2.3 and 2.5 → the published StableMatching.Instance n (men and women both Fin n, preferences as rank bijections, rank 0 = most preferred), Matching n = Fin n ≃ Fin n, StableCount.MatchingLE / StableCount.Covers; reason: the same objects: a rank bijection is a strict total order, and MatchingLE/Covers are Definitions 2.3 and 2.5 word for word
--   - encoding: s^±_{m,D}(k) = ∞ and undefined cones/supports when the k-th rotation does not exist → ssize : ℕ∞ with ⊤ for ∞; principalCone and supp are Option-valued (none = undefined); reason: Lean convention; comparisons such as s ≥ d+2 are true at ⊤, as the paper uses them
--   - encoding: averages over (μ, m) uniform on Ω × M with D = D(μ) → avgDm: (1/(|Ω| n)) ∑_{μ ∈ Ω} ∑_m f(D(μ), m), with |Ω| = StableCount.numStable I; reason: the uniform average written out; same value
--   - generalization: uniform averages on pointed matchings Ω × M, requiring n ≥ 1 → also n = 0, with es I = pc I = 0 by the totalized finite-average definition; reason: for n ≥ 1 this is exactly the source; at n = 0 the three inequalities reduce to 0 ≤ 1, 0 ≤ 2 and 0 ≤ 4/3
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Lemma 5.13, p. 30 (PDF 32)

import Mathlib
import Definitions.Def_StableCountSub3_Credits

open StableMatching

namespace StableCountSub3

/-- Lemma 5.13: `e_s ≤ 1 + p_c`, `e_s ≤ 2(1 − p_c)` and `e_s ≤ 4/3`. -/
theorem lemma_5_13 {n : ℕ} (I : Instance n) :
    es I ≤ 1 + pc I ∧ es I ≤ 2 * (1 - pc I) ∧ es I ≤ 4 / 3 := by sorry

end StableCountSub3
