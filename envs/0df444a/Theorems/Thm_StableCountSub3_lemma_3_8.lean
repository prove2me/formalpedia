-- Prove2me | Theorems.Thm_StableCountSub3_lemma_3_8
-- name    : StableCountSub3.lemma_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:49:19.965298+00:00
-- url     : https://prove2.me/theorems/de669c2f-71f8-45aa-8d98-3698755586d9
-- title:
--   Lemma 3.8 — support size: $s^\pm_{m,D}(k)\ge k+1$
-- statement:
--   For every downset $D$, man $m$, direction $\pm$ and positive integer $k$, $s^\pm_{m,D}(k)\ge k+1$ (in $\mathbb N\cup\{\infty\}$; $s=\infty$ when the $k$-th rotation does not exist).
--
--   Differences from the source:
--   - encoding: men M = {m1,…,mn}, women W = {w1,…,wn}, strict complete preference lists, perfect matchings as bijections M → W, the order ⪯ and the cover relation ⋖ of Definitions 2.3 and 2.5 → the published StableMatching.Instance n (men and women both Fin n, preferences as rank bijections, rank 0 = most preferred), Matching n = Fin n ≃ Fin n, StableCount.MatchingLE / StableCount.Covers; reason: the same objects: a rank bijection is a strict total order, and MatchingLE/Covers are Definitions 2.3 and 2.5 word for word
--   - encoding: rotations (μ∖μ′, μ′∖μ) of covers, the rotation poset (ℛ, ⪯), D(μ), μ_D, μ_m-opt → Rot n = pair of finsets of (man, woman) pairs; RotLE from "precedes (first occurrence) in every rotation sequence"; Dof, muOf and mopt chosen by Classical.choice among the objects the page describes; reason: Definitions 2.6–2.9 transcribed; the choices are unique by Theorem 2.10 and Theorem 2.4, and the fallback values are never reached
--   - encoding: s^±_{m,D}(k) = ∞ and undefined cones/supports when the k-th rotation does not exist → ssize : ℕ∞ with ⊤ for ∞; principalCone and supp are Option-valued (none = undefined); reason: Lean convention; comparisons such as s ≥ d+2 are true at ⊤, as the paper uses them
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Lemma 3.8, p. 16 (PDF 18)

import Mathlib
import Definitions.Def_StableCountSub3_Cones

open StableMatching

namespace StableCountSub3

/-- Lemma 3.8 (support size): `s^±_{m,D}(k) ≥ k + 1` for every positive integer `k`
(`s = ∞` when the `k`-th rotation does not exist). -/
theorem lemma_3_8 {n : ℕ} (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D)
    (m : Fin n) (dir : Dir) (k : ℕ) (hk : 1 ≤ k) :
    ((k + 1 : ℕ) : ℕ∞) ≤ ssize I D m dir k := by sorry

end StableCountSub3
