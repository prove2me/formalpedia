-- Prove2me | Theorems.Thm_StableCountSub3_theorem_2_11
-- name    : StableCountSub3.theorem_2_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:48:33.449993+00:00
-- url     : https://prove2.me/theorems/3467dd0d-3a51-4963-9e49-bd4ae8af0571
-- title:
--   Theorem 2.11 — uniqueness of rotations, $m$-chains, and partner changes under elimination
-- statement:
--   For every instance $I$:
--   (i) for every pair $(m,w)$ there is at most one rotation $\rho\in\mathcal R$ with $(m,w)\in\mu\setminus\mu'$ (the first component of $\rho$);
--   (ii) for every man $m$, any two rotations of $C_m$ are comparable in $\preceq$;
--   (iii) if eliminating $\rho$ transforms $\mu$ into $\mu'$, every man $v\in M(\rho)$ strictly prefers $\mu(v)$ to $\mu'(v)$, and every man $v\notin M(\rho)$ has $\mu'(v)=\mu(v)$.
--
--   Differences from the source:
--   - encoding: men M = {m1,…,mn}, women W = {w1,…,wn}, strict complete preference lists, perfect matchings as bijections M → W, the order ⪯ and the cover relation ⋖ of Definitions 2.3 and 2.5 → the published StableMatching.Instance n (men and women both Fin n, preferences as rank bijections, rank 0 = most preferred), Matching n = Fin n ≃ Fin n, StableCount.MatchingLE / StableCount.Covers; reason: the same objects: a rank bijection is a strict total order, and MatchingLE/Covers are Definitions 2.3 and 2.5 word for word
--   - encoding: rotations (μ∖μ′, μ′∖μ) of covers, the rotation poset (ℛ, ⪯), D(μ), μ_D, μ_m-opt → Rot n = pair of finsets of (man, woman) pairs; RotLE from "precedes (first occurrence) in every rotation sequence"; Dof, muOf and mopt chosen by Classical.choice among the objects the page describes; reason: Definitions 2.6–2.9 transcribed; the choices are unique by Theorem 2.10 and Theorem 2.4, and the fallback values are never reached
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Theorem 2.11, p. 9 (PDF 11)

import Mathlib
import Definitions.Def_StableCountSub3_RotationPoset

open StableMatching

namespace StableCountSub3

/-- Theorem 2.11 (uniqueness of rotations and `m`-chains), all three clauses. -/
theorem theorem_2_11 {n : ℕ} (I : Instance n) :
    -- (i) each pair `(m, w)` lies in `μ \ μ'` for at most one rotation
    (∀ (m w : Fin n), ∀ ρ ∈ rotations I, ∀ ρ' ∈ rotations I,
      (m, w) ∈ ρ.1 → (m, w) ∈ ρ'.1 → ρ = ρ') ∧
    -- (ii) the `m`-chain `C_m` is a chain of `(ℛ, ⪯)`
    (∀ m : Fin n, ∀ ρ ∈ mchain I m, ∀ ρ' ∈ mchain I m, RotLE I ρ ρ' ∨ RotLE I ρ' ρ) ∧
    -- (iii) eliminating `ρ` strictly worsens the partner of every man of `M(ρ)` and leaves the
    -- other men's partners unchanged
    (∀ (μ μ' : Matching n) (ρ : Rot n), Eliminates I μ ρ μ' →
      (∀ v ∈ participants ρ, I.manPrefers v (μ v) (μ' v)) ∧
      (∀ v, v ∉ participants ρ → μ' v = μ v)) := by sorry

end StableCountSub3
