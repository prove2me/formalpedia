-- Prove2me | Theorems.Thm_RandOrderCSP_theorem_1_1
-- name    : RandOrderCSP.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:10:33.423512+00:00
-- url     : https://prove2.me/theorems/6fb22fef-9cca-49c2-8163-ab2a9ef5be92
-- title:
--   Theorem 1.1 — dichotomy theorem for random-order streaming
-- statement:
--   Let $k\ge2$, let $\Sigma$ be a finite set, let $\Gamma\subseteq\{0,1\}^{\Sigma^k}$ be a set of predicates, and let $0\le\beta<\gamma\le1$.
--
--   1. If the basic LP solves $\text{MAX-CSP}_{\beta,\gamma}(\Gamma)$, then for every $\varepsilon>0$ and $c\in\mathbb N$ there is a family of randomized streaming algorithms of space $s(n)\le C(\log_2(n+2))^3$, depending on $n$ only, that solves $\text{MAX-CSP}_{\beta-\varepsilon,\gamma+\varepsilon}(\Gamma)$ on instances with $n$ variables and at most $n^c$ constraints in uniformly random order, with failure $\delta(n)\to0$.
--   2. If $\text{MAX-CSP}_{\beta,\gamma}(\Gamma)$ has an integrality gap, then for every $\varepsilon>0$ there is $C_\varepsilon\in\mathbb N$ such that any family of algorithms $A(n,m)$ with space budget $s(n)$ that solves $\text{MAX-CSP}_{\beta+\varepsilon,\gamma-\varepsilon}(\Gamma)$ on instances with $n$ variables and at most $C_\varepsilon n$ constraints with failure $\delta(n)\to0$ has $s(n)\ne o(n)$. If $\gamma=1$, the same holds for $\text{MAX-CSP}_{\beta+\varepsilon,1}(\Gamma)$.
--
--   So the basic LP decides the random-order single-pass complexity of every Max-CSP, with an exponential gap in space.
--
--   Differences from the source:
--   - generalization: lower bullet: the basic LP does not solve MAX-CSP_{β,γ}(Γ) → HasIntegralityGap Γ β γ; reason: the printed hypothesis implies the gap (proved in the sanity file), and §4.3 uses only the gap instance
--   - encoding: O_c(log³ n)-space, o(n)-space, 1 − o(1) → ∃ C with s n ≤ C (log₂(n+2))³; ¬(s = o(n)) over every family; an explicit δ → 0; reason: quantifiers made explicit; n+2 covers small n and is the same order as n → ∞
--   - encoding: NO case opt^CSP(Φ) < β on p.1, ≤ β on p.2 and p.14 → opt ≤ β′; reason: over ∀ε the two readings are equivalent by sandwiching at ε and ε/2
--   - encoding: the first bit of the final state as output (p.1) → an output function of the final state (§3.5, p.15); reason: the paper gives both forms, saying "say, the first bit"; §3.5 is the formal model
--   - encoding: Σ a finite set; instances with at most n^c or C_ε n constraints → [Nonempty Sig]; m ≥ 1; reason: an instance needs an assignment and a nonempty edge set (p.13)
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), Theorem 1.1, p.3

import Mathlib
import Definitions.Def_RandOrderCSP_BasicLPSolves
import Definitions.Def_RandOrderCSP_HasIntegralityGap
import Definitions.Def_RandOrderCSP_Solves

open Filter Asymptotics

namespace RandOrderCSP

/-- **Theorem 1.1 (dichotomy theorem for random-order streaming).** Singer, Tulsiani, Velusamy, *A dichotomy
theorem for approximating CSPs in random-order streams*, STOC 2027 submission (manuscript sha256
3aca9d2f…), Theorem 1.1, p.3.

**Formalization Note.** `O_c(log³ n)`, `o(n)` and `1 - o(1)` are explicit: the upper bullet produces, for
each `ε` and `c`, one family `A n` with `s n ≤ C (log₂(n+2))³` and failure function `δ → 0`. The algorithm
sees `n` only (`fun n _ => A n`). The lower bullet says that every family `A n m` with one budget `s n`
solving the problem with `δ → 0` has `¬ (s = o(n))`. The hypothesis of the lower bullet is the integrality
gap (p.14), which `¬ BasicLPSolves` implies. One `C_ε` serves both lower conclusions. -/
theorem theorem_1_1 {k : ℕ} (hk : 2 ≤ k) {Sig : Type} [Fintype Sig] [DecidableEq Sig] [Nonempty Sig]
    (Γ : Set ((Fin k → Sig) → Bool)) (β γ : ℝ) (hβ : 0 ≤ β) (hβγ : β < γ) (hγ : γ ≤ 1) :
    (BasicLPSolves Γ β γ → ∀ ε : ℝ, 0 < ε → ∀ c : ℕ,
      ∃ (C : ℝ) (s : ℕ → ℕ) (A : (n : ℕ) → RandAlg (Constraint k Sig n) (s n)) (δ : ℕ → ℝ),
        Tendsto δ atTop (nhds 0) ∧
        (∀ n, (s n : ℝ) ≤ C * Real.logb 2 ((n : ℝ) + 2) ^ 3) ∧
        Solves Γ (β - ε) (γ + ε) (fun n => n ^ c) s (fun n _ => A n) δ) ∧
    (HasIntegralityGap Γ β γ → ∀ ε : ℝ, 0 < ε → ∃ Cε : ℕ,
      (∀ (s : ℕ → ℕ) (A : (n m : ℕ) → RandAlg (Constraint k Sig n) (s n)) (δ : ℕ → ℝ),
        Tendsto δ atTop (nhds 0) →
        Solves Γ (β + ε) (γ - ε) (fun n => Cε * n) s A δ →
        ¬ ((fun n => (s n : ℝ)) =o[atTop] fun n => (n : ℝ))) ∧
      (γ = 1 → ∀ (s : ℕ → ℕ) (A : (n m : ℕ) → RandAlg (Constraint k Sig n) (s n)) (δ : ℕ → ℝ),
        Tendsto δ atTop (nhds 0) →
        Solves Γ (β + ε) 1 (fun n => Cε * n) s A δ →
        ¬ ((fun n => (s n : ℝ)) =o[atTop] fun n => (n : ℝ)))) := by sorry

end RandOrderCSP
