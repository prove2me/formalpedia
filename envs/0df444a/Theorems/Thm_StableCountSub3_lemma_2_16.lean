-- Prove2me | Theorems.Thm_StableCountSub3_lemma_2_16
-- name    : StableCountSub3.lemma_2_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:48:26.62178+00:00
-- url     : https://prove2.me/theorems/2f3ed0cc-d8e7-4d70-b571-ba86d6fdc017
-- title:
--   Lemma 2.16 — non-revisiting property
-- statement:
--   Let $D$ be a downset and $m$ a man. If $\rho\in\min P^+(D)$ then $T_m(D\cup\{\rho\})=T_m(D)+\mathbf 1_{\rho\in C_m}$; if $\rho\in\min P^-(D)$ then $T_m(D\setminus\{\rho\})=T_m(D)-\mathbf 1_{\rho\in C_m}$. Consequently, along an execution in a single direction starting at $\mu_D$ (a sequence of matchings $f(0)=\mu_D,f(1),\dots,f(K)$ in which each step eliminates a rotation, $f(i)\lessdot f(i+1)$, or each step undoes one, $f(i+1)\lessdot f(i)$), no man returns to a woman after leaving her: if $f(k)(v)=f(i)(v)$ with $i\le j\le k$ then $f(j)(v)=f(i)(v)$.
--
--   Differences from the source:
--   - encoding: men M = {m1,…,mn}, women W = {w1,…,wn}, strict complete preference lists, perfect matchings as bijections M → W, the order ⪯ and the cover relation ⋖ of Definitions 2.3 and 2.5 → the published StableMatching.Instance n (men and women both Fin n, preferences as rank bijections, rank 0 = most preferred), Matching n = Fin n ≃ Fin n, StableCount.MatchingLE / StableCount.Covers; reason: the same objects: a rank bijection is a strict total order, and MatchingLE/Covers are Definitions 2.3 and 2.5 word for word
--   - encoding: rotations (μ∖μ′, μ′∖μ) of covers, the rotation poset (ℛ, ⪯), D(μ), μ_D, μ_m-opt → Rot n = pair of finsets of (man, woman) pairs; RotLE from "precedes (first occurrence) in every rotation sequence"; Dof, muOf and mopt chosen by Classical.choice among the objects the page describes; reason: Definitions 2.6–2.9 transcribed; the choices are unique by Theorem 2.10 and Theorem 2.4, and the fallback values are never reached
--   - encoding: T_m(D ∖ {ρ}) = T_m(D) − 1_{ρ∈C_m} → the same equation cast to ℤ; reason: avoids truncated natural-number subtraction; same content
--   - reading: "during an execution of rotations in a single direction, either forward or backward, no man returns to a woman after leaving her" → for any sequence f(0) = μ_D, …, f(K) of successive covers (forward) or successive reverse covers (backward), f(k)(v) = f(i)(v) with i ≤ j ≤ k implies f(j)(v) = f(i)(v); reason: an execution is a sequence of eliminations (or undoings), each a cover; "returns after leaving" is a repeat of a partner with a different one in between
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Lemma 2.16, p. 11 (PDF 13)

import Mathlib
import Definitions.Def_StableCountSub3_RotationPoset

open StableMatching

namespace StableCountSub3

/-- Lemma 2.16 (non-revisiting property). -/
theorem lemma_2_16 {n : ℕ} (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D)
    (m : Fin n) :
    (∀ ρ, IsMinOut I D .fwd ρ →
      boundary I m (insert ρ D) = boundary I m D + (if ρ ∈ mchain I m then 1 else 0)) ∧
    (∀ ρ, IsMinOut I D .bwd ρ →
      (boundary I m (D.erase ρ) : ℤ) = boundary I m D - (if ρ ∈ mchain I m then 1 else 0)) ∧
    -- consequence: along an execution from `μ_D` in one direction no man returns to a woman
    -- after leaving her (forward: successive eliminations; backward: successive undoings)
    (∀ (f : ℕ → Matching n) (K : ℕ), f 0 = muOf I D →
      (∀ i < K, StableCount.Covers I (f i) (f (i + 1))) →
      ∀ v : Fin n, ∀ i j k, i ≤ j → j ≤ k → k ≤ K → f k v = f i v → f j v = f i v) ∧
    (∀ (f : ℕ → Matching n) (K : ℕ), f 0 = muOf I D →
      (∀ i < K, StableCount.Covers I (f (i + 1)) (f i)) →
      ∀ v : Fin n, ∀ i j k, i ≤ j → j ≤ k → k ≤ K → f k v = f i v → f j v = f i v) := by sorry

end StableCountSub3
