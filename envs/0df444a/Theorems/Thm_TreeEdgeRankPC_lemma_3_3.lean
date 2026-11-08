-- Prove2me | Theorems.Thm_TreeEdgeRankPC_lemma_3_3
-- name    : TreeEdgeRankPC.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:04.258602+00:00
-- url     : https://prove2.me/theorems/92de82a2-27f0-47b9-8c35-9464e5f8a9a4
-- title:
--   Lemma 3.3 — exchange and increment facts for $\kappa$, and $\mathrm{crit}(T_v)=\mathrm{CR}(\mathrm{crit}(T_{v_1}),\dots,\mathrm{crit}(T_{v_d}))$
-- statement:
--   Let $A$ and $C$ be sets of ranks, and let $v$ have children $v_1,\dots,v_d$ in a tree $T$ rooted at $r$. Then:
--
--   1. If $\mathrm{wt}(A)<\mathrm{wt}(C)$, the rank $c=\max(A\triangle C)$ satisfies $c\in C\setminus A$ and $\kappa(A,c)\subseteq C$.
--   2. For every positive rank $c\notin A$, $\ \mathrm{wt}(\kappa(A,c))\ge\mathrm{wt}(A)+1$.
--   3. Critical rankings of the $T_{v_i}$ together with a critical assignment of ranks to the branches form a critical ranking of $T_v$, i.e.
--   $$\mathrm{crit}(T_v)=\mathrm{CR}(\mathrm{crit}(T_{v_1}),\dots,\mathrm{crit}(T_{v_d})).$$
--
--   So a critical set can be computed bottom-up from the critical sets of the children.
--
--   Differences from the source:
--   - encoding: a rooted tree T = (V, E) → `T : SimpleGraph V` with `T.IsTree`, `Fintype V`, and a root `r : V`; reason: Lean's graph type; the same objects
--   - encoding: the subtree T_v and branches as trees → graphs on the same vertex type with vertices outside isolated; reason: rankings, visibility and critical sets depend only on edges and walks from the root, so nothing changes
--   - encoding: fixed rankings of the T_{v_i} and ranks c_i → one function ρ, with c_i = ρ s(v, v_i); reason: these live on pairwise disjoint edge sets
--   - encoding: sets of ranks → finite sets of positive integers (`IsRankSet`); reason: ranks are positive by definition, and `wt` is meant on such sets
--   - encoding: a critical assignment "gives a ranking of T_v that is valid" → `ValidAssignment` (positive admissible ranks with pairwise disjoint κ sets) in `IsCriticalAssignment` and `CR`; reason: by Proposition 3.2 these are exactly the assignments giving a valid ranking when the A_i are visible sets of valid subtree rankings, as the crit(T_{v_i}) are
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), Lemma 3.3, p.11

import Mathlib
import Definitions.Def_TreeEdgeRankPC_EdgeRanking
import Definitions.Def_TreeEdgeRankPC_CriticalSet

namespace TreeEdgeRankPC

/-- **Lemma 3.3**, §3.1, p.11, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…): "Let A and C be sets of ranks, and let v have children v1, ..., vd. We
have the following: (a) If wt(A) < wt(C), the rank c = max(A△C) satisfies c ∈ C \ A and κ(A, c) ⊆ C. (b) For
every positive rank c ∉ A, we have wt(κ(A, c)) ≥ wt(A) + 1. (c) Critical rankings of the T_{vi} together with a
critical assignment of ranks to the branches form a critical ranking of T_v, i.e., crit(T_v) =
CR(crit(T_{v1}), ..., crit(T_{vd}))."

**Formalization Note.** Sets of ranks are finite sets of positive integers (`IsRankSet`). In (a), `c` is the
greatest element of the symmetric difference, which is nonempty since `wt(A) < wt(C)` forces `A ≠ C`. Part (c)
has both of its printed clauses: the statement on rankings, and the identity of sets. -/
theorem lemma_3_3 {V : Type*} [Fintype V] (T : SimpleGraph V) (hT : T.IsTree) (r v : V) :
    (∀ A C : Finset ℕ, IsRankSet A → IsRankSet C → wt A < wt C →
      ∃ c, IsGreatest (↑(symmDiff A C) : Set ℕ) c ∧ c ∈ C \ A ∧ kappa A c ⊆ C) ∧
    (∀ (A : Finset ℕ) (c : ℕ), IsRankSet A → 1 ≤ c → c ∉ A → wt A + 1 ≤ wt (kappa A c)) ∧
    (∀ ρ : Sym2 V → ℕ, (∀ c ∈ children T r v, IsCriticalRanking (subtree T r c) c ρ) →
      IsCriticalAssignment (children T r v) (fun c => crit (subtree T r c) c)
        (fun c => ρ s(v, c)) →
      IsCriticalRanking (subtree T r v) v ρ) ∧
    crit (subtree T r v) v =
      CR (children T r v) (fun c => crit (subtree T r c) c) := by sorry

end TreeEdgeRankPC
