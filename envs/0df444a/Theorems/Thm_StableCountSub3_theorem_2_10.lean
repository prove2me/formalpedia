-- Prove2me | Theorems.Thm_StableCountSub3_theorem_2_10
-- name    : StableCountSub3.theorem_2_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:48:33.460308+00:00
-- url     : https://prove2.me/theorems/5094851d-c712-4c12-a7a7-204a0d820d9c
-- title:
--   Theorem 2.10 — rotation representation: downsets of $(\mathcal R,\preceq)$ ↔ stable matchings
-- statement:
--   For every instance $I$:
--   (i) for every stable $\mu$ there is a rotation sequence from $\mu_{m\text{-opt}}$ to $\mu$, every such sequence eliminates exactly the set $D(\mu)$, and $D(\mu)$ is a downset of $(\mathcal R,\preceq)$;
--   (ii) every downset $D$ has a linear extension, and eliminating the rotations of $D$ from $\mu_{m\text{-opt}}$ along any linear extension is a rotation sequence ending at the same stable matching $\mu_D$;
--   (iii) $\mu\mapsto D(\mu)$ and $D\mapsto\mu_D$ are mutually inverse bijections between $\Omega$ and the downsets: $\mu_{D(\mu)}=\mu$ for stable $\mu$, and $\mu_D$ is stable with $D(\mu_D)=D$ for every downset $D$;
--   (iv) if eliminating $\rho$ transforms $\mu$ into $\mu'$, then $\rho\notin D(\mu)$ and $D(\mu')=D(\mu)\cup\{\rho\}$; conversely, if $\mu$ is stable, $\rho\in\mathcal R\setminus D(\mu)$ and $D(\mu)\cup\{\rho\}$ is a downset, then $\rho$ is exposed in $\mu$ and eliminating it yields $\mu_{D(\mu)\cup\{\rho\}}$.
--
--   Differences from the source:
--   - encoding: men M = {m1,…,mn}, women W = {w1,…,wn}, strict complete preference lists, perfect matchings as bijections M → W, the order ⪯ and the cover relation ⋖ of Definitions 2.3 and 2.5 → the published StableMatching.Instance n (men and women both Fin n, preferences as rank bijections, rank 0 = most preferred), Matching n = Fin n ≃ Fin n, StableCount.MatchingLE / StableCount.Covers; reason: the same objects: a rank bijection is a strict total order, and MatchingLE/Covers are Definitions 2.3 and 2.5 word for word
--   - encoding: rotations (μ∖μ′, μ′∖μ) of covers, the rotation poset (ℛ, ⪯), D(μ), μ_D, μ_m-opt → Rot n = pair of finsets of (man, woman) pairs; RotLE from "precedes (first occurrence) in every rotation sequence"; Dof, muOf and mopt chosen by Classical.choice among the objects the page describes; reason: Definitions 2.6–2.9 transcribed; the choices are unique by Theorem 2.10 and Theorem 2.4, and the fallback values are never reached
--   - reading: (i) "D(μ) is uniquely determined" → a rotation sequence from μ_m-opt to μ exists, and every such sequence has element set D(μ); reason: D(μ) is defined as the set eliminated from μ_m-opt to μ, which presupposes such a sequence; uniqueness means every sequence gives the same set
--   - reading: (ii) "eliminating its rotations from μm-opt along any linear extension yields a unique stable matching μD" → a linear extension exists, and for every linear extension l, IsRotSeq I (mopt I) l (muOf I D); reason: makes "any" non-vacuous; the endpoint of a rotation sequence is determined by its start and its rotations, so one common endpoint is uniqueness
--   - reading: (iv) "Eliminating a rotation ρ from μ corresponds to adding ρ to D(μ)" → both directions: an elimination μ → μ′ has ρ ∉ D(μ) and D(μ′) = D(μ) ∪ {ρ}; and ρ ∈ ℛ ∖ D(μ) with D(μ) ∪ {ρ} a downset is exposed in μ, with result μ_{D(μ)∪{ρ}}; reason: "corresponds" read as a two-way correspondence, the stronger reading; both directions are classical [GI89]
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Theorem 2.10, p. 9 (PDF 11)

import Mathlib
import Definitions.Def_StableCountSub3_RotationPoset

open StableMatching

namespace StableCountSub3

/-- Theorem 2.10 (rotation representation, [GI89]), all four clauses. -/
theorem theorem_2_10 {n : ℕ} (I : Instance n) :
    -- (i) `D(μ)` is uniquely determined and is a downset
    (∀ μ : Matching n, I.IsStable μ →
      (∃ l, IsRotSeq I (mopt I) l μ) ∧
      (∀ l, IsRotSeq I (mopt I) l μ → l.toFinset = Dof I μ) ∧
      IsDownset I (Dof I μ)) ∧
    -- (ii) every downset has a linear extension, and eliminating along any of them is legal and
    -- yields the same stable matching `μ_D`
    (∀ D, IsDownset I D →
      (∃ l, IsLinExt I D l) ∧
      ∀ l, IsLinExt I D l → IsRotSeq I (mopt I) l (muOf I D)) ∧
    -- (iii) `μ ↦ D(μ)` and `D ↦ μ_D` are mutually inverse bijections
    (∀ μ : Matching n, I.IsStable μ → muOf I (Dof I μ) = μ) ∧
    (∀ D, IsDownset I D → I.IsStable (muOf I D) ∧ Dof I (muOf I D) = D) ∧
    -- (iv) eliminating `ρ` from `μ` corresponds to adding `ρ` to `D(μ)`
    (∀ (μ μ' : Matching n) (ρ : Rot n), Eliminates I μ ρ μ' →
      ρ ∉ Dof I μ ∧ Dof I μ' = insert ρ (Dof I μ)) ∧
    (∀ μ : Matching n, I.IsStable μ → ∀ ρ ∈ rotations I, ρ ∉ Dof I μ →
      IsDownset I (insert ρ (Dof I μ)) → Eliminates I μ ρ (muOf I (insert ρ (Dof I μ)))) := by sorry

end StableCountSub3
