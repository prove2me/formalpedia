-- Prove2me | Theorems.Thm_QPACLarge_Supplement_theorem_4_1
-- name    : QPACLarge.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:25:55.450556+00:00
-- url     : https://prove2.me/theorems/39b4fdf9-437e-48d3-a701-e0a7c3e66b60
-- title:
--   Theorem 4.1 — with $q$ queries, success at agreement $1/2+\gamma$, $\gamma>q/(2N)$, is at most $1/2$ on average and for some target
-- statement:
--   Let $N = 2^n$ and let $A$ be a randomized classical learner that makes at most $q$ (possibly adaptive) membership queries to a target $f : \{0,1\}^n \to \{0,1\}$ and outputs a hypothesis $h$. Then for every $\gamma > q/(2N)$:
--
--   1. the success probability averaged over a uniformly random target is at most $1/2$,
--   $$
--   \mathbb E_{f\sim \mathrm{ALL}_n}\Big[\Pr_A\Big[\Pr_{x\sim U_n}[h(x)=f(x)] \ge \frac12+\gamma\Big]\Big] \le \frac12;
--   $$
--   2. consequently, there is a target $f \in \mathrm{ALL}_n$ with $\Pr_A\big[\Pr_{x\sim U_n}[h(x)=f(x)] \ge \frac12+\gamma\big] \le \frac12$.
--
--   Here $\mathrm{ALL}_n$ is the set of all $2^{2^n}$ Boolean functions on $n$ bits. No bound is placed on the running time of $A$ or on the size of $h$. This is Theorem 4.1 of the paper together with Theorem 1.4 Item (i): reaching advantage $\Omega(2^{-n/2})$ with success probability above $1/2$ on all of $\mathrm{ALL}_n$ requires $\Omega(2^{n/2})$ classical membership queries, in contrast with the single quantum example of Theorem 3.3.
--
--   **Formalization Note** The learner is a probability distribution over deterministic adaptive query trees with at most $q$ queries on every path (the published `RandDecisionTree` with `RandMakesAtMost`), whose leaves carry an arbitrary hypothesis $h : \{0,1\}^n \to \{0,1\}$, as in the published Lemma 5.1.
--
--   Differences from the source:
--   - generalization: a randomized classical learner making at most $q$ membership queries and outputting a deterministic Boolean circuit $h$ → any probability distribution over decision trees with at most $q$ queries on every path and any hypothesis $h : \{0,1\}^n \to \{0,1\}$ at the leaves; reason: a learner with fixed coins is such a tree and a circuit determines its function; footnote 5 and p.30 place no bound on time or on the size of $h$
--   - generalization: $n \ge 1$ (Section 2.1: $N = 2^n$ for $n \ge 1$) → every $n \in \mathbb N$, including $n = 0$; reason: the statement for $n \ge 1$ is the instance; the transcript argument also holds at $N = 1$
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Theorem 4.1, p.30 (and Theorem 1.4 Item (i), p.6, footnote 5; proof pp.30–31)

import Mathlib
import Definitions.Def_QPACLarge_treeSuccess
import Definitions.Def_QPACLarge_agreement

namespace QPACLarge.Supplement

open QAlgorithms QPACLarge

/-- **Theorem 4.1 (Classical Query Lower Bound)**, together with **Theorem 1.4 Item (i)**.
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*,
arXiv:2610.23268 (held file sha256 e749e7c9…), Theorem 4.1, p.30: "Let `A` be a randomized
classical learner that makes at most `q` membership queries to a target `f ∈ ALLₙ` and outputs a
deterministic Boolean circuit `h`. For every `γ > q/(2N)`,
`E_{f∼ALLₙ}[Pr_A[Pr_{x∼Uₙ}[h(x) = f(x)] ≥ 1/2 + γ]] ≤ 1/2`. Consequently, `A` has success
probability at most `1/2` at this correlation regime for some target `f ∈ ALLₙ`." Theorem 1.4
Item (i), p.6, is the consequence (with `q/2^{n+1} = q/(2N)`); footnote 5: no restriction on the
running time of `A` or on the size of `h`.

**Formalization Note.** The learner is any randomized decision tree over `{0,1}ⁿ` with at most `q`
queries on every path (the published `RandDecisionTree`, `RandMakesAtMost`) and any hypothesis
`h : {0,1}ⁿ → {0,1}` at its leaves, as in the published `QPACLarge.lemma_5_1`; every learner of the
paper is such a tree. `N = 2ⁿ`; the average over `f` is uniform over the `2^{2ⁿ}` functions. The
statement is made for every `n`, including `n = 0`. -/
theorem theorem_4_1 (n q : ℕ) (R : RandDecisionTree (Qubits n) Bool (Qubits n → Bool))
    (hR : RandMakesAtMost R q) (γ : ℝ) (hγ : (q : ℝ) / (2 * 2 ^ n) < γ) :
    ((2 : ℝ) ^ (2 ^ n))⁻¹ * ∑ f : Qubits n → Bool,
        treeSuccess R f (fun h => 1 / 2 + γ ≤ agreement f h) ≤ 1 / 2 ∧
      ∃ f : Qubits n → Bool, treeSuccess R f (fun h => 1 / 2 + γ ≤ agreement f h) ≤ 1 / 2 := by sorry

end QPACLarge.Supplement
