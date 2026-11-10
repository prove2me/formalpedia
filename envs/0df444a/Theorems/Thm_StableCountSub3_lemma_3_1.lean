-- Prove2me | Theorems.Thm_StableCountSub3_lemma_3_1
-- name    : StableCountSub3.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:50:16.387055+00:00
-- url     : https://prove2.me/theorems/95bb0949-57ad-42e4-93c1-58187bed0313
-- title:
--   Lemma 3.1 — entropy bound of the random-reveal model
-- statement:
--   For every instance $I$, $\log|\Omega|\le\sum_{m\in M}E_{D,U}[\log N_m(D,U)]$, where $\mu$ is uniform on $\Omega$, $D=D(\mu)$, $U$ is uniform on $[0,1]^n$ independently of $\mu$, and $N_m(D,U)$ is the number of values $T_m(E)$ over downsets $E$ with $T_v(E)=T_v(D)$ for all $v$ with $U_v<U_m$. The logarithm is natural.
--
--   Differences from the source:
--   - encoding: men M = {m1,…,mn}, women W = {w1,…,wn}, strict complete preference lists, perfect matchings as bijections M → W, the order ⪯ and the cover relation ⋖ of Definitions 2.3 and 2.5 → the published StableMatching.Instance n (men and women both Fin n, preferences as rank bijections, rank 0 = most preferred), Matching n = Fin n ≃ Fin n, StableCount.MatchingLE / StableCount.Covers; reason: the same objects: a rank bijection is a strict total order, and MatchingLE/Covers are Definitions 2.3 and 2.5 word for word
--   - encoding: rotations (μ∖μ′, μ′∖μ) of covers, the rotation poset (ℛ, ⪯), D(μ), μ_D, μ_m-opt → Rot n = pair of finsets of (man, woman) pairs; RotLE from "precedes (first occurrence) in every rotation sequence"; Dof, muOf and mopt chosen by Classical.choice among the objects the page describes; reason: Definitions 2.6–2.9 transcribed; the choices are unique by Theorem 2.10 and Theorem 2.4, and the fallback values are never reached
--   - encoding: E_{D,U}, μ uniform on Ω, U Lebesgue on [0,1]^n; |Ω| → avgDU = (1/numStable I) ∑_{μ∈Ω} ∫ f(D(μ),U) d(unifCube n); |Ω| = StableCount.numStable I; reason: the expectation written out; same value
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Lemma 3.1, p. 12 (PDF 14)

import Mathlib
import Definitions.Def_StableCountSub3_RandomReveal

open StableMatching

namespace StableCountSub3

/-- Lemma 3.1 (entropy bound): `log |Ω| ≤ ∑_{m ∈ M} E_{D,U}[log N_m(D, U)]`. -/
theorem lemma_3_1 {n : ℕ} (I : Instance n) :
    Real.log (StableCount.numStable I : ℝ) ≤
      ∑ m : Fin n, avgDU I fun D U => Real.log (numCand I D m U) := by sorry

end StableCountSub3
