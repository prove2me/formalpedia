-- Prove2me | Theorems.Thm_WeldedPath_Supplement_theorem_3_12
-- name    : WeldedPath.Supplement.theorem_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:17:43.058462+00:00
-- url     : https://prove2.me/theorems/dee1738c-048d-41be-ab60-d9a180dc2412
-- title:
--   Theorem 3.12 — $p_{\mathrm{wt}}=O(p_{\mathrm{cross}}+q/N_l)$ when $N_l\ge 80(q+1)$
-- statement:
--   Let $n$ be even, $l\in[2,n-4]$ and $N_l=2^{n-l}$, and fix a valid welded trees instance. For a $q$-query algorithm $A$ ($q\ge1$) with output map, let $p_{\mathrm{wt}}$ be the success probability of the standard-oracle verifier (Algorithm 3.9, $\sigma\sim D_{\mathrm{prod}}$) and $p_{\mathrm{cross}}$ the probability that running $A$ with the exact compressed oracle $\widehat{\mathrm{cpWT}}$ from the empty database leaves a recorded crossing (Algorithm 3.10). If $N_l\ge 80(q+1)$, then
--   $$
--   p_{\mathrm{wt}}=O\!\left(p_{\mathrm{cross}}+\frac{q}{N_l}\right),
--   $$
--   with one absolute constant: there is $C>0$ such that $p_{\mathrm{wt}}\le C\,(p_{\mathrm{cross}}+q/2^{n-l})$ for every such $n$, $l$, instance, workspace, $q$, algorithm and output map.
--
--   The theorem reduces pathfinding with the real oracle to recording a crossing of the middle columns in the compressed database, which §4 shows is unlikely.
--
--   **Formalization Note** Algorithms are published `QAlgorithms.QueryAlg`s with a finite workspace; $p_{\mathrm{wt}}$ is `pWt`, $p_{\mathrm{cross}}$ is `pCross` for the same algorithm.
--
--   Differences from the source:
--   - generalization: one fixed instance G_n with one fixed coloring (pp.14–15) → every valid weld (one bipartite cycle on the leaves) and every proper 3-coloring, with C independent of them; reason: the fixed instance is one of them
--   - reading: O(p_cross + q/N_l) → one absolute constant C > 0 for all even n, l ∈ [2, n − 4], instances, workspaces, q ≥ 1, algorithms and output maps; reason: the bound is uniform in all parameters
--   - reading: any algorithm A making q queries → q ≥ 1; reason: the paper's standing convention that every algorithm makes at least one query (p.8); at q = 0 p_cross = 0 while p_wt can be positive
--   - encoding: algorithm A_q O ⋯ A_1 O A_0|0⟩ and its output → QAlgorithms.QueryAlg with any unit start state and finite workspace; the output list is a function of the computational-basis outcome; reason: a unit start state is |0⟩ followed by A_0; measuring the whole register is the general output
--   - encoding: work register Z of Ô^wt_∘ and the conventions of p.20 → v, f as (2n+1)-bit strings, ⊥ = 0, edge j of a class written as j + 1, labels written as 1, …, M, each skip the identity on its control branch; reason: the source fixes ⊥ = 0 and nonzero edge indices and leaves the widths open; Z returns to |0, 0⟩ under I_Z†
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), Theorem 3.12, (47), p.24

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_WeldedPath_Supplement_pWt
import Definitions.Def_WeldedPath_Supplement_pCross

namespace WeldedPath

namespace Supplement

open QAlgorithms

/-- **Theorem 3.12** (Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic
Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…),
Theorem 3.12, p.24). For any algorithm `A` making `q` queries where `N_l ≥ 80(q + 1)`,
`p_wt = O(p_cross + q/N_l)` (47), with `N_l = 2^{n−l}`.

**Formalization Note.**
1. `p_wt` is the success probability of Algorithm 3.9 (`pWt`: `σ ∼ D_prod`, the verifier with the
   `m ≤ 2q + 1` / `m > 2q + 1` split) and `p_cross` that of Algorithm 3.10 (`pCross`: the same
   algorithm `A`, run with `\widehat{cpWT}` from `|⊥⟩_I`, then `Π_Cross`).
2. `O(·)` is one absolute constant `C`, chosen before `n`, `l`, the instance, the workspace, `q`,
   the algorithm and its output map.
3. The standing assumptions of §3.1 (p.14): `n` even and `l ∈ [2, n − 4]`; the instance is any
   valid weld with a proper 3-coloring (`WeldedInstance.IsValid`). `q ≥ 1` ("every algorithm
   makes at least 1 query", p.8).
4. The algorithm is the published `QAlgorithms.QueryAlg` with query register `(2n+1)`-bit label ×
   color, `(2n+1)`-bit answer register and any finite workspace `W`; its output is read off the
   final measurement by `out`. -/
theorem theorem_3_12 :
    ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (q : ℕ), 1 ≤ q →
      ∀ (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
        (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
          List (Fin 3 × Qubits (2 * n + 1))),
      80 * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n - l) →
      pWt l G A out ≤ C * (pCross l G A + (q : ℝ) / (2 : ℝ) ^ (n - l)) := by sorry

end Supplement

end WeldedPath
