-- Prove2me | Theorems.Thm_VecKnapsackMitM_Main_lemma_4_5
-- name    : VecKnapsackMitM.Main.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:35:09.289389+00:00
-- url     : https://prove2.me/theorems/27426972-27a5-4c97-bc27-52e63049b0fa
-- title:
--   Lemma 4.5 — Orthogonal range searching with maximum-profit queries
-- statement:
--   There are an admissible build program, an admissible query program and one constant $C$ such that for every dimension $D\ge1$ and every $m$ objects, object $k$ with a point $x_k\in(\mathbb R\cup\{-\infty,\infty\})^D$ and a profit $p_k\in\mathbb R$ (input `orsBuildInput`): the build halts within $C^D\cdot M\log_2^{D-1}M$ steps, $M=\max(m,2)$, and from its final state, for every axis-aligned closed box $R=[a_1,b_1]\times\dots\times[a_D,b_D]$ with ends in $\mathbb R\cup\{\pm\infty\}$ written at the address the build designates (`queryState`), the query program halts within $C^D\log_2^DM$ steps with $N[1]$ a correct answer: $k+1$ for an object $k$ with $x_k\in R$ and $p_k$ maximum among such objects, or $0$ ($\bot$) if no object has its point in $R$.
--
--   The post-build state satisfies an invariant `Ready`. Every query from any `Ready` state returns a correct answer and a `Ready` state within the query bound, so arbitrarily many adaptive queries can be made consecutively.
--
--   Differences from the source:
--   - generalization: "For every d ∈ N … in time O(n log^{d−1} n) … in time O(log^d n)" → D ≥ 1; one build program, one query program and one constant C for all D; build ≤ C^D·M·log₂^{D−1} M, query ≤ C^D·log₂^D M; reason: positive dimension is the reading of N here; choosing the programs and a dimension-exponential constant uniformly strengthens the fixed-dimension claim and specializes to its complete bounds (INSIGHTS I2)
--   - reading: n inside the bounds → M = max(m, 2); reason: log 1 = 0 makes the printed bounds 0 at m = 1 (INSIGHTS I1); identical for m ≥ 2
--   - encoding: a set C of objects with points and profits; a query range; the answer S or ⊥ → objects Fin m, EReal coordinates encoded by tags, orsBuildInput; queryState writes each box at N[0]; N[1] returns object k+1 or 0; a state predicate Ready contains the build result and is preserved by every query; reason: Ready makes the online interface explicit: each query starts from the preceding query result, retains a valid structure, and receives the same time bound without copying or rebuilding
--   - generalization: an algorithm on the RealRAM (§2, printed p. 8) → an admissible program (VecBalPoly.Admissible: rational literals, no √, no random draws) of the published unit-cost real RAM MatMulTimeLP, which has no floor, no real-to-index conversion and no index multiplication; time = executed instructions including the final halt; reason: fewer primitives only make the existential claim harder; every such program is a deterministic RealRAM algorithm with the same step count, so the Lean statement specializes to the paper's
-- source:
--   Bringmann, Kulik, Węgrzycki (2026), Fine-Grained Complexity of Approximating Vector Knapsack: A Faster Algorithm and Equivalence with k-SUM in 2D, STOC 2027 submission, SHA-256 966f42f7…10ac98; Lemma 4.5, printed p. 18 (PDF 19)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecKnapsackMitM_Main_Machine
import Definitions.Def_VecKnapsackMitM_Main_Geometry

namespace VecKnapsackMitM.Main

open MatMulTimeLP

/-- Bringmann, Kulik, Węgrzycki (2026), Lemma 4.5 (Orthogonal Range Searching), printed p. 18
(PDF 19). There are a build program `Pb`, a query program `Pq` and a constant `C` such that for
every dimension `D ≥ 1` and every `m` objects with points `x k ∈ (ℝ ∪ {−∞, ∞})^D` and real
profits `pr k`: the build halts within `C^D · M · log₂^{D−1} M` steps (`M = max(m, 2)`), and
the final state satisfies an invariant `Ready`. From every state satisfying `Ready`, a query
with a closed box `[lo, hi]` halts within `C^D · log₂^D M` steps with a correct answer in
`N[1]` and another state satisfying `Ready`. Thus arbitrarily many adaptive queries run
consecutively, each with the same time bound and without rebuilding or copying the memory. -/
theorem lemma_4_5 :
    ∃ Pb Pq : Program, VecBalPoly.Admissible Pb ∧ VecBalPoly.Admissible Pq ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (D m : ℕ), 1 ≤ D → ∀ (x : Fin m → Fin D → EReal) (pr : Fin m → ℝ),
        ∃ tb : ℕ, IsHalted Pb (run Pb (orsBuildInput D m x pr) tb) ∧
          (tb : ℝ) + 1 ≤ C ^ D * NN m * Real.logb 2 (NN m) ^ (D - 1) ∧
          ∃ Ready : State → Prop,
            Ready (run Pb (orsBuildInput D m x pr) tb) ∧
            ∀ s₀ : State, Ready s₀ → ∀ lo hi : Fin D → EReal,
              RunsWithin Pq (queryState s₀ D lo hi)
                (C ^ D * Real.logb 2 (NN m) ^ D)
                (fun s => ORSAnswerOK x pr lo hi (s.N 1) ∧ Ready s) := by sorry

end VecKnapsackMitM.Main
