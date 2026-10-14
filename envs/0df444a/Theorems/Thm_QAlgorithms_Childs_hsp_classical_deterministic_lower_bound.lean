-- Prove2me | Theorems.Thm_QAlgorithms_Childs_hsp_classical_deterministic_lower_bound
-- name    : QAlgorithms.Childs.hsp_classical_deterministic_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:32:34.963116+00:00
-- url     : https://prove2.me/theorems/e0362b0f-d424-4ff8-a16b-44e9a61305bd
-- title:
--   Ω(√N) deterministic classical queries for the HSP with N trivially intersecting subgroups
-- statement:
--   In the hidden subgroup problem (HSP) on a finite group $G$, an algorithm has black-box access to a function $f : G \to S$, where $S$ is a finite set, promised to **hide** some unknown subgroup $H \le G$:
--
--   $$
--   f(x) = f(y) \iff x^{-1}y \in H \qquad (x, y \in G).
--   $$
--
--   The goal is to determine $H$. A deterministic classical algorithm is a decision tree: it queries group elements $g_1, g_2, \dots$ adaptively, each query returning $f(g_\ell) \in S$, and finally outputs a subgroup of $G$. It **solves the HSP** if, for every subgroup $H \le G$ and every $f$ hiding $H$, its output is $H$. Its query count on input $f$ is the number of queries it makes on $f$.
--
--   **Theorem.** There are an absolute constant $c > 0$ and a threshold $N_0$ such that the following holds for every $N \ge N_0$. Let $G$ be a finite group and $S$ a finite set with $|S| \ge |G|$, and suppose $G$ has a family $\mathcal H$ of $N$ distinct subgroups any two of which have only the identity in common, i.e. $H \cap K = \{1\}$ for all distinct $H, K \in \mathcal H$. Then every deterministic classical algorithm that solves the HSP on $G$ (with values in $S$) makes, on some input $f$ hiding some subgroup of $G$,
--
--   $$
--   \#\text{queries}(f) \ge c\sqrt{N}.
--   $$
--
--   The theorem shows that the HSP is classically hard whenever the group has many trivially intersecting subgroups (for example Simon's problem), in contrast with efficient quantum algorithms for abelian groups.
--
--   **Formalization Note** The algorithm outputs the subgroup itself rather than a generating set, which changes nothing for a query lower bound. The condition $|S| \ge |G|$ makes every subgroup of $G$ hideable; the proof's adversary labels each new query with a fresh value, and with a very small $S$ (say $|S| = 1$) only $H = G$ can be hidden, so the bound would fail. The constants $c$ and $N_0$ are chosen before the group, the set $S$, the family and the algorithm. The threshold $N_0$ is needed because for the trivial group $N = 1$ and no queries are needed. The phrase "whose only common element is the identity" is read pairwise, as in the section's "trivially intersecting subgroups" and as the proof needs when it counts at most $t(t-1)$ non-identity values $g_j^{-1}g_k$ against $N$ subgroups. Read as $\bigcap \mathcal H = \{1\}$, the theorem is false: in the cyclic group of squarefree order $p_1\cdots p_k$, all $2^k$ subgroups intersect trivially, yet $k+1$ queries determine $H$.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 30, Theorem 5.1. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Fourier
set_option autoImplicit false

namespace QAlgorithms.Childs

universe u v

/-- **Childs, Theorem 5.1** (PDF p. 30, proof pp. 30–31). Suppose that `G` has a set `ℋ` of `N`
subgroups whose only common element is the identity. Then to solve the hidden subgroup problem,
a deterministic classical computer must make `Ω(√N)` queries.

The HSP (§5.3, p. 30): a black-box `f : G → S`, `S` a finite set, is promised to hide some
subgroup `H ≤ G`, i.e. `f x = f y ↔ x⁻¹ * y ∈ H` (`Hides`, eq. (5.1)); the goal is to learn `H`.
A deterministic classical algorithm is a decision tree that queries group elements adaptively,
receives values in `S`, and outputs a subgroup of `G` (outputting `H` itself rather than a
generating set; equivalent for counting queries). "Solves the HSP" means: for every subgroup
`H ≤ G` and every `f` hiding `H`, the output is `H`. The query count on input `f` is the number
of queries along the path `f` follows.

Conventions made explicit: `G` is finite, and `|S| ≥ |G|`, so that every subgroup of `G` can be
hidden (the proof's adversary answers each new query with a fresh label; with a small `S`, e.g.
`|S| = 1`, only `H = G` can be hidden and zero queries suffice). `Ω` is read with a threshold
`N₀`, and the constants `c`, `N₀` are absolute: they precede the group, the set `S`, the family
and the algorithm. The lower bound is "every correct algorithm has a hard input".

"Whose only common element is the identity" is read as in the section's lead-in ("a large
number of *trivially intersecting* subgroups") and as the proof uses it: any two distinct members
of `ℋ` meet only in the identity. The proof counts the at most `t(t − 1)` non-identity values
`g_j⁻¹ g_k` against the `N` members of `ℋ`, and that count needs each such value to lie in at most
one member. Read instead as `⋂ ℋ = {1}`, the theorem is false: in the cyclic group of squarefree
order `p₁ ⋯ p_k`, all `2^k` subgroups intersect in `{1}`, yet querying `1` and one element of
each prime order `p_i` (`k + 1` queries) determines `H`. -/
theorem hsp_classical_deterministic_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (G : Type u) [Group G] [Fintype G] (S : Type v) [Fintype S],
        Fintype.card G ≤ Fintype.card S →
        ∀ ℋ : Finset (Subgroup G), ℋ.card = N →
        (ℋ : Set (Subgroup G)).Pairwise (fun H K => H ⊓ K = ⊥) →
        ∀ A : DecisionTree G S (Subgroup G),
          (∀ (H : Subgroup G) (f : G → S), Hides f H → A.eval f = H) →
          ∃ (H : Subgroup G) (f : G → S), Hides f H ∧
            c * Real.sqrt (N : ℝ) ≤ (A.queries f : ℝ) := by
  sorry

end QAlgorithms.Childs
