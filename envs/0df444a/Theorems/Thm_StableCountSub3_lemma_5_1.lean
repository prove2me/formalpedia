-- Prove2me | Theorems.Thm_StableCountSub3_lemma_5_1
-- name    : StableCountSub3.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:49:27.502267+00:00
-- url     : https://prove2.me/theorems/6b165dd8-fc80-4299-9943-13012bf5d981
-- title:
--   Lemma 5.1 — cones with three-man support
-- statement:
--   Let $D$ be a downset, fix a direction, and let $K$ be a cone with $|S(K)|=3$. Then (1) $K$ contains at most two rotations; (2) if $K=\{\rho_1,\rho_2\}$ with $\rho_1\neq\rho_2$, executed in the chosen direction with $\rho_1$ first ($\rho_2$ does not precede $\rho_1$ in the outward order), then either $\rho_1,\rho_2$ are swaps on two different pairs of men, or there is an ordering $(a,b,c)$ of three men for which both $\rho_1$ and $\rho_2$ are the 3-cycle $(a,b,c)$ (the same cyclic orientation).
--
--   Differences from the source:
--   - encoding: men M = {m1,…,mn}, women W = {w1,…,wn}, strict complete preference lists, perfect matchings as bijections M → W, the order ⪯ and the cover relation ⋖ of Definitions 2.3 and 2.5 → the published StableMatching.Instance n (men and women both Fin n, preferences as rank bijections, rank 0 = most preferred), Matching n = Fin n ≃ Fin n, StableCount.MatchingLE / StableCount.Covers; reason: the same objects: a rank bijection is a strict total order, and MatchingLE/Covers are Definitions 2.3 and 2.5 word for word
--   - encoding: rotations (μ∖μ′, μ′∖μ) of covers, the rotation poset (ℛ, ⪯), D(μ), μ_D, μ_m-opt → Rot n = pair of finsets of (man, woman) pairs; RotLE from "precedes (first occurrence) in every rotation sequence"; Dof, muOf and mopt chosen by Classical.choice among the objects the page describes; reason: Definitions 2.6–2.9 transcribed; the choices are unique by Theorem 2.10 and Theorem 2.4, and the fallback values are never reached
--   - encoding: "their execution consists of …" (execution = eliminate forward, undo backward; the operations as permutations of partners) → Takes / IsSwapOn / Is3CycleOn in the chosen direction, with ρ₁ executed first (¬ outLT dir ρ₂ ρ₁); reason: the operations of §5.1 written as partner transfers; an execution order is a linear extension of K
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Lemma 5.1, p. 25 (PDF 27)

import Mathlib
import Definitions.Def_StableCountSub3_Cones

open StableMatching

namespace StableCountSub3

/-- Lemma 5.1: a cone `K` with `|S(K)| = 3` contains at most two rotations, and two rotations,
executed in the outward direction (`ρ₁` not after `ρ₂`), are two swaps on distinct pairs of men
or two 3-cycles with the same cyclic orientation. -/
theorem lemma_5_1 {n : ℕ} (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D)
    (dir : Dir) (K : Finset (Rot n)) (hK : IsCone I D dir K) (hS : (support K).card = 3) :
    K.card ≤ 2 ∧
    ∀ ρ₁ ρ₂ : Rot n, K = {ρ₁, ρ₂} → ρ₁ ≠ ρ₂ → ¬ outLT I dir ρ₂ ρ₁ →
      (∃ a b c d : Fin n, IsSwapOn dir ρ₁ a b ∧ IsSwapOn dir ρ₂ c d ∧
        ({a, b} : Finset (Fin n)) ≠ {c, d}) ∨
      (∃ a b c : Fin n, Is3CycleOn dir ρ₁ a b c ∧ Is3CycleOn dir ρ₂ a b c) := by sorry

end StableCountSub3
