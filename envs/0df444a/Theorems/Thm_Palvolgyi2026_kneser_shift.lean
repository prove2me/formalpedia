-- Prove2me | Theorems.Thm_Palvolgyi2026_kneser_shift
-- name    : Palvolgyi2026.kneser_shift
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T13:20:37.682195+00:00
-- url     : https://prove2.me/theorems/88e50ee2-adbf-41ca-a769-564877b2c29d
-- title:
--   Pálvölgyi's Kneser-shift theorem (Theorem 4) — for prime p, every r-colouring of the Kneser-shift graph KSh_p(n, k) has a monochromatic edge once n − pk ≥ C(p, r)
-- statement:
--   Let $p = q + 1$ be a prime and $r \in \mathbb N$. There is a constant $C$ (depending only on $p$ and $r$) such that for all $n, k$ with $pk + C \le n$, every colouring $c$ of the $(p-1)$-tuples of subsets of $\{0, \dots, n-1\}$ with $r$ colours admits $p$ pairwise disjoint $k$-element sets $A_1, \dots, A_p$ with
--   $$c(A_1, \dots, A_{p-1}) = c(A_2, \dots, A_p).$$
--
--   Pálvölgyi, p. 4: “The vertices of the Kneser-shift graph $\mathrm{KSh}_p(n,k)$ are the ordered $(p-1)$-tuples $(A_1, \dots, A_{p-1})$ of pairwise disjoint sets from $\binom{[n]}{k}$, and there is an edge between $(A_1, \dots, A_{p-1})$ and $(A_2, \dots, A_p)$ whenever $A_1$ and $A_p$ are also pairwise disjoint.” “Theorem 4 (Kneser-shift theorem). $\chi(\mathrm{KSh}_p(n,k)) \to \infty$ as $n - pk \to \infty$ for every prime $p$. In other words, for every prime $p$ and every $r \in \mathbb N$ there is a (least) constant $C(p,r)$, depending only on $p$ and $r$, such that whenever $n - pk$ is at least $C(p,r)$, every $r$-coloring of the vertices of $\mathrm{KSh}_p(n,k)$ admits pairwise disjoint $A_1, \dots, A_p \in \binom{[n]}{k}$ for which $c(A_1, \dots, A_{p-1}) = c(A_2, \dots, A_p)$.”
--
--   For $p = 2$ this is the statement that the chromatic number of the Kneser graph $\mathrm{KG}(n, k)$ tends to infinity with $n - 2k$ (Lovász). The paper derives the theorem from Ziegler's $\mathbb Z_p$-Tucker lemma (Section 4) and uses it to prove its Dense Block theorem (Theorem 11), which is [`RamseyDisambig.Spherical.theorem_11`](https://prove2.me/theorems/0310d004-a0be-4466-8ddd-452786c9e5f9).
--
--   **Formalization note.** The prime is written $q + 1$, and $n - pk \ge C$ is written $pk + C \le n$. The colouring is given on all $(p-1)$-tuples of finite subsets of `Fin n` rather than on the vertices of $\mathrm{KSh}_p(n,k)$ only; since any colouring of the vertices extends to all tuples and the conclusion only evaluates $c$ at vertices, the two forms are equivalent. The tuples $(A_1, \dots, A_{p-1})$ and $(A_2, \dots, A_p)$ are `fun i => A i.castSucc` and `fun i => A i.succ` for `A : Fin (q + 1) → Finset (Fin n)`.
-- source:
--   Pálvölgyi, D., A nearcircumsphere-Ramsey theorem for solvable transitive configurations, arXiv:2608.10865v2 (2026), https://arxiv.org/abs/2608.10865, p. 4, Theorem 4 (Kneser-shift theorem)

import Mathlib

namespace Palvolgyi2026

theorem kneser_shift (q : ℕ) (hp : (q + 1).Prime) (r : ℕ) :
    ∃ C : ℕ, ∀ n k : ℕ, (q + 1) * k + C ≤ n →
      ∀ c : (Fin q → Finset (Fin n)) → Fin r,
        ∃ A : Fin (q + 1) → Finset (Fin n),
          (∀ i, (A i).card = k) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
            c (fun i => A i.castSucc) = c (fun i => A i.succ) := by
  sorry

end Palvolgyi2026
