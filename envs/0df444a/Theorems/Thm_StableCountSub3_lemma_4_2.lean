-- Prove2me | Theorems.Thm_StableCountSub3_lemma_4_2
-- name    : StableCountSub3.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:51:05.096529+00:00
-- url     : https://prove2.me/theorems/9328aaef-a1b8-4601-aa5f-951752745b36
-- title:
--   Lemma 4.2 — entropy bound from tail-probability deficits
-- statement:
--   Fix a downset $D$, a man $m$ and $x=U_m\in(0,1)$, with $L=L_m(D,U)$, $R=R_m(D,U)$ and $a_k,b_k,w_k$ as in Definition 4.1. Then the series $\sum_{k\ge1}(a_k+b_k)w_k$ converges, and
--   $E_{L,R}[\log(1+L+R)]\le E_{G_1,G_2}[\log(1+G_1+G_2)]-\sum_{k\ge1}(a_k+b_k)w_k$,
--   where all expectations are conditional on $D$ and $U_m=x$, and $G_1,G_2$ are independent with $P(G=k)=x(1-x)^k$.
--
--   Differences from the source:
--   - encoding: men M = {m1,…,mn}, women W = {w1,…,wn}, strict complete preference lists, perfect matchings as bijections M → W, the order ⪯ and the cover relation ⋖ of Definitions 2.3 and 2.5 → the published StableMatching.Instance n (men and women both Fin n, preferences as rank bijections, rank 0 = most preferred), Matching n = Fin n ≃ Fin n, StableCount.MatchingLE / StableCount.Covers; reason: the same objects: a rank bijection is a strict total order, and MatchingLE/Covers are Definitions 2.3 and 2.5 word for word
--   - encoding: s^±_{m,D}(k) = ∞ and undefined cones/supports when the k-th rotation does not exist → ssize : ℕ∞ with ⊤ for ∞; principalCone and supp are Option-valued (none = undefined); reason: Lean convention; comparisons such as s ≥ d+2 are true at ⊤, as the paper uses them
--   - encoding: E_{L,R}[·] and E_{G1,G2}[·] conditional on D and U_m = x; ∑_{k≥1} → expAt m x (integral over the other priorities); benchmark x = ∑_{(j,k)∈ℕ²} x(1−x)^j x(1−x)^k log(1+j+k); ∑_{k≥1} as ∑′ over k+1; reason: the expectations written as an integral and a series of nonnegative terms; index shift
--   - reading: the real number ∑_{k≥1}(a_k+b_k)w_k (finite, as the proof notes) → Summable conjunct, then tsum; reason: a Lean tsum of a non-summable series is 0; asserting summability states that the sum is the finite sum the page uses
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Lemma 4.2, p. 20 (PDF 22)

import Mathlib
import Definitions.Def_StableCountSub3_Savings

open StableMatching

namespace StableCountSub3

/-- Lemma 4.2 (entropy bound from tail-probability deficits): conditional on `D` and
`U_m = x ∈ (0, 1)`, `E[log(1 + L + R)] ≤ E[log(1 + G₁ + G₂)] − ∑_{k ≥ 1} (a_k + b_k) w_k`
(the deficit series is summable). -/
theorem lemma_4_2 {n : ℕ} (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D)
    (m : Fin n) (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    Summable (fun k : ℕ =>
      (deficitL I D m x (k + 1) + deficitR I D m x (k + 1)) * weight x (k + 1)) ∧
    expAt m x (fun U => Real.log (1 + (Lm I D m U : ℝ) + (Rm I D m U : ℝ))) ≤
      benchmark x - ∑' k : ℕ,
        (deficitL I D m x (k + 1) + deficitR I D m x (k + 1)) * weight x (k + 1) := by sorry

end StableCountSub3
