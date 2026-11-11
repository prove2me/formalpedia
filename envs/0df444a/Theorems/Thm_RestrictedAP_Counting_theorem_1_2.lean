-- Prove2me | Theorems.Thm_RestrictedAP_Counting_theorem_1_2
-- name    : RestrictedAP.Counting.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:20:05.096914+00:00
-- url     : https://prove2.me/theorems/6fd5ee61-3a68-4d69-8261-e099f3316a0e
-- title:
--   Theorem 1.2 — dense subsets of $\mathbb F_p^n$ contain a positive fraction of the somewhat restricted 3-APs
-- statement:
--   For every prime $p\ge3$ and every $\alpha>0$ there are $\beta>0$ and $n_0\in\mathbb N$ such that for every $n\ge n_0$ and every $A\subseteq\mathbb F_p^n$ of density at least $\alpha$ (that is, $|A|\ge\alpha p^n$),
--   $$\Pr_{x\in\mathbb F_p^n,\ a\in\{0,1,2\}^n}\big[x,\ x+a,\ x+2a\in A\big]\ \ge\ \beta,$$
--   where $x$ and $a$ are independent and uniform, $a$ is read coordinatewise in $\mathbb F_p$, and $a=0$ is included. Here $\beta$ and $n_0$ depend only on $p$ and $\alpha$.
--
--   This is the paper's main result: the counting version of the density theorem for somewhat restricted 3-APs, where the standard averaging argument that turns existence into counting fails because the patterns depend on the basis.
--
--   Differences from the source:
--   - encoding: Pr over independent uniform x ∈ F_p^n, a ∈ {0,1,2}^n → the number of (x, a) ∈ (Fin n → ZMod p) × (Fin n → Fin 3) with x, x + a, x + 2a ∈ A, divided by p^n · 3^n; a cast coordinatewise into ZMod p; reason: uniform probability on a finite set; same instances
--   - encoding: A has density at least α → α · p^n ≤ |A|; reason: density = |A|/p^n
--   - reading: 'there exists β > 0, such that for large enough n' → ∃ β > 0, ∃ n₀, ∀ n ≥ n₀ (β and n₀ after p and α only); reason: the printed quantifier order; p is 'a prime of constant size' (§1.1)
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 3, Theorem 1.2

import Mathlib
import Definitions.Def_RestrictedAP_Counting_SomewhatRestricted3APCount

namespace RestrictedAP.Counting

/-- **Theorem 1.2** (p. 3). For every prime `p ≥ 3` and every `α > 0` there are `β > 0` and
`n₀` such that for every `n ≥ n₀` and every `A ⊆ F_p^n` with `|A| ≥ α p^n`,
`Pr_{x ∈ F_p^n, a ∈ {0,1,2}^n} [x, x + a, x + 2a ∈ A] ≥ β` (`x`, `a` independent and uniform,
`a` cast coordinatewise into `F_p`, `a = 0` included). -/
theorem theorem_1_2 (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (α : ℝ) (hα : 0 < α) :
    ∃ β : ℝ, 0 < β ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ A : Finset (Fin n → ZMod p), α * (p : ℝ) ^ n ≤ (A.card : ℝ) →
        β ≤ somewhatRestricted3APProb p n A := by sorry

end RestrictedAP.Counting
