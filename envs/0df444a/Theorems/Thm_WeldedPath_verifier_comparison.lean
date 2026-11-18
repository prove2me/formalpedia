-- Prove2me | Theorems.Thm_WeldedPath_verifier_comparison
-- name    : WeldedPath.verifier_comparison
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-17T16:15:45.483257+00:00
-- url     : https://prove2.me/theorems/17eb2ec8-f5d2-4d78-beaf-30a173b7f606
-- title:
--   Loop-erased path verification transfers success to the product distribution
-- statement:
--   Let $n\ge16$ be even, $2\le l\le n-4$, and let $G$ be a valid welded-tree instance with a proper three-coloring. There is an absolute constant $C>0$ such that every $q\ge1$ query algorithm $A$, with any finite workspace and output map $o$ to lists of colored labels, admits another output map $o'$ satisfying
--   $$
--   \Pr_{D_{\rm sing}}[o\text{ is an entrance--exit walk}]
--   \le C\left(p_{\rm wt}(A,o')+\frac{nq^2}{2^n}\right).
--   $$
--   Here $p_{\rm wt}$ is the acceptance probability of Algorithm 3.9 under the product distribution. The new output map may erase loops using only the output labels, without further queries or knowledge of the sampled oracle. Its existential quantifier accommodates the walk-based success predicate while the verifier requires distinct path labels. This statement isolates the verifier and distribution-comparison part of the proof of Theorem 4.1.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/pdf/2611.05912v1. Section 3.3, p.23 (loop removal), Algorithm 3.9, p.24; Lemma 4.13, pp.42-43; Section 4.5, p.44, first two inequalities after Eq. (78). The accumulated-error equation is numbered (75) in the PDF and (78) in https://arxiv.org/html/2611.05912v1. The loop-erased output is explicit because the target success predicate counts walks.

import Mathlib
import Definitions.Def_WeldedPath_Supplement_pWt

namespace WeldedPath

open QAlgorithms Supplement

theorem verifier_comparison :
    ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (q : ℕ), 1 ≤ q →
      ∀ (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
        (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
          List (Fin 3 × Qubits (2 * n + 1))),
      ∃ out' : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
          List (Fin 3 × Qubits (2 * n + 1)),
      G.successProb l A out ≤
        C * (pWt l G A out' + (n : ℝ) * (q : ℝ) ^ 2 / (2 : ℝ) ^ n) := by sorry

end WeldedPath
