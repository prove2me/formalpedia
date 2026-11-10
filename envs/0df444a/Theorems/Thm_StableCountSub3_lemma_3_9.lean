-- Prove2me | Theorems.Thm_StableCountSub3_lemma_3_9
-- name    : StableCountSub3.lemma_3_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:50:57.710492+00:00
-- url     : https://prove2.me/theorems/0bbaeaf6-7984-4ed3-b803-ef0e965d4140
-- title:
--   Lemma 3.9 — conditional tails of $L_m$ and $R_m$
-- statement:
--   Fix a downset $D$, a man $m$, a positive integer $k$ and $x\in(0,1)$. Conditional on $D$ and $U_m=x$ (the other priorities independent uniform on $[0,1]$),
--   $P(L_m(D,U)\ge k)=(1-x)^{s^-_{m,D}(k)-1}\le(1-x)^k$ and $P(R_m(D,U)\ge k)=(1-x)^{s^+_{m,D}(k)-1}\le(1-x)^k$,
--   where $(1-x)^{\infty-1}$ is read as $0$.
--
--   Differences from the source:
--   - encoding: men M = {m1,…,mn}, women W = {w1,…,wn}, strict complete preference lists, perfect matchings as bijections M → W, the order ⪯ and the cover relation ⋖ of Definitions 2.3 and 2.5 → the published StableMatching.Instance n (men and women both Fin n, preferences as rank bijections, rank 0 = most preferred), Matching n = Fin n ≃ Fin n, StableCount.MatchingLE / StableCount.Covers; reason: the same objects: a rank bijection is a strict total order, and MatchingLE/Covers are Definitions 2.3 and 2.5 word for word
--   - encoding: s^±_{m,D}(k) = ∞ and undefined cones/supports when the k-th rotation does not exist → ssize : ℕ∞ with ⊤ for ∞; principalCone and supp are Option-valued (none = undefined); reason: Lean convention; comparisons such as s ≥ d+2 are true at ⊤, as the paper uses them
--   - encoding: P(· | D, U_m = x) → probAt m x E = measure under unifCube n of {U : E(U with U_m set to x)}; reason: conditioning on U_m = x for independent uniform priorities is integrating the others over [0,1]^{n−1}; same value
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Lemma 3.9, p. 16 (PDF 18)

import Mathlib
import Definitions.Def_StableCountSub3_Savings

open StableMatching

namespace StableCountSub3

/-- Lemma 3.9: conditional on `D` and `U_m = x`, `P(L ≥ k) = (1 − x)^{s⁻(k) − 1} ≤ (1 − x)^k` and
`P(R ≥ k) = (1 − x)^{s⁺(k) − 1} ≤ (1 − x)^k`, with `(1 − x)^{∞ − 1} = 0`. -/
theorem lemma_3_9 {n : ℕ} (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D)
    (m : Fin n) (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    probAt m x (fun U => k ≤ Lm I D m U) = tailPow x (ssize I D m .bwd k) ∧
    tailPow x (ssize I D m .bwd k) ≤ (1 - x) ^ k ∧
    probAt m x (fun U => k ≤ Rm I D m U) = tailPow x (ssize I D m .fwd k) ∧
    tailPow x (ssize I D m .fwd k) ≤ (1 - x) ^ k := by sorry

end StableCountSub3
