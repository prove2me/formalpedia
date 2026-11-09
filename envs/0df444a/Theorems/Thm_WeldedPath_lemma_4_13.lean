-- Prove2me | Theorems.Thm_WeldedPath_lemma_4_13
-- name    : WeldedPath.lemma_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:25:04.918634+00:00
-- url     : https://prove2.me/theorems/48c64f49-ee2b-4012-9872-a0de8d72379a
-- title:
--   Lemma 4.13 — from the single-cycle to the product distribution
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $n$ be even, $l\in[2,n-4]$, $G_n$ a valid welded trees instance, and $A$ a quantum algorithm making $q\ge 1$ queries to $O^{(wt)}_\sigma$ that accepts when its final measurement outcome lies in a fixed set. Writing $p_D(A)$ for its acceptance probability when $\sigma\sim D$,
--   $$
--   p_{D_{\mathrm{sing}}}(A)\ \le\ C\Big(p_{D_{\mathrm{prod}}}(A)+\frac{n\,q^2}{N}\Big),\qquad N=2^n .
--   $$
--
--   Conditioning the weld on being one cycle changes acceptance probabilities only by the additive $O(nq^2/N)$, so the analysis can work with the product distribution.
--
--   Differences from the source:
--   - reading: acceptance probability of a quantum algorithm → probability that the final computational-basis outcome lies in a fixed set acc not depending on σ; reason: an algorithm accepts on a fixed set of measurement outcomes
--   - reading: O(p_{D_prod}(A) + n·q²/N) → one absolute constant C chosen before n, l, the instance, the workspace, q, A and acc; reason: the bound is uniform in all parameters
--   - generalization: the standing assumption (49) of §4 → not assumed; reason: the proof (pp.41–42) uses only Lemma 3.2 and the hybrid argument; adding (49) gives the source's statement
--   - generalization: one fixed instance and coloring (pp.14–15) → every valid weld and proper 3-coloring; reason: the fixed instance is one of them
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), Lemma 4.13, p.41

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_WeldedPath_successProb

namespace WeldedPath

open QAlgorithms

/-- **Lemma 4.13** (Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, arXiv:2611.05912
(sha256 b31400a0…), Lemma 4.13, p.41). Let `p_D(A)` be the acceptance probability of a quantum
algorithm `A` making `q ≥ 1` queries to an oracle sampled from `D`. Then
`p_{D_sing}(A) = O(p_{D_prod}(A) + n·q²/N)`, `N = 2^n`.

**Formalization Note.** `A` accepts when the final computational-basis measurement gives an
outcome in the fixed set `acc` (which does not depend on `σ`). `O(·)` is one absolute constant
`C`, chosen before `n`, `l`, the instance, the workspace, `q`, `A` and `acc`. The standing
assumptions of §3.1 (`n` even, `l ∈ [2, n − 4]`) are hypotheses; (49) is not. -/
theorem lemma_4_13 :
    ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (q : ℕ), 1 ≤ q →
      ∀ (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
        (acc : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W → Prop),
      G.probOver l (G.singSupport l) A (fun _ => acc) ≤
        C * (G.probOver l (G.prodSupport l) A (fun _ => acc) +
          (n : ℝ) * (q : ℝ) ^ 2 / 2 ^ n) := by sorry

end WeldedPath
