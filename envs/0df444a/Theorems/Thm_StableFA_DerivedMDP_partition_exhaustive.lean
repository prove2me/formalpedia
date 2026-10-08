-- Prove2me | Theorems.Thm_StableFA_DerivedMDP_partition_exhaustive
-- name    : StableFA.DerivedMDP.partition_exhaustive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:10.734765+00:00
-- url     : https://prove2.me/theorems/bc076676-2cb2-49cb-adec-bb4d1157b497
-- title:
--   §4, p. 10 — if all policies are proper, the partition S_1, S_2, … by distance from the goal is exhaustive
-- statement:
--   Let $M$ be a finite nondiscounted Markov decision process with cost-free absorbing goal state $1$ in which every policy is proper. Define the layers $S_1=\{1\}$, $U_k=\bigcup_{j<k}S_j$ and, for $k\ge 2$,
--   $$S_k=\Bigl\{x\;\Bigm|\;x\notin U_k\ \wedge\ \min_a\max_{y\in U_k}P(\delta(x,a)=y)>0\Bigr\}.$$
--   Then every state lies in some layer: for every non-goal state $x$ there is an index $k$ with $x\in S_k$.
--
--   The report attributes this to Bertsekas and Tsitsiklis [BT89]. It makes the layer index $k(x)$, the "distance from the goal", well defined, and with it the notion of a self-weighted averager.
--
--   **Formalization Note** "All policies proper" quantifies over stationary policies (functions from states to admissible actions, p. 3). The goal state lies in $S_1$ by definition, so only non-goal states are quantified.
-- source:
--   Gordon, Stable Function Approximation in Dynamic Programming, Tech. Rep. CMU-CS-95-103, Carnegie Mellon University (1995), p. 10, §4, "Bertsekas and Tsitsiklis show that this partitioning is exhaustive"

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_DerivedMDP_Setting

namespace StableFA.DerivedMDP

theorem partition_exhaustive {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C)
    (hproper : ∀ μ : Fin n → C, (∀ i, μ i ∈ M.U i) → IsProper M μ) :
    ∀ i : Fin n, ∃ k : ℕ, some i ∈ layer M k := by sorry

end StableFA.DerivedMDP
