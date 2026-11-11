-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_sparse_prune
-- name    : SparsestCutOracle.Main.sparse_prune
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:45:04.338968+00:00
-- url     : https://prove2.me/theorems/ae27424f-f5e7-49f2-b3e5-56692c9c0270
-- title:
--   Theorem 8 — SparsePrune with a sparse removed cut
-- statement:
--   Let $G$ be $\psi$-expanding for $\psi\ge0$, delete edge positions $F$ of total capacity $W$, and write $H=G\setminus F$. If $W\le\psi(V)/96$, every pair of valid 2-fair outputs in the stated SparsePrune trace returns a cut $P$ satisfying
--
--   $$\psi(P)\le48W\le\psi(V)/2,\qquad
--   H[V\setminus P]\text{ is }\psi\text{-expanding with quality }1/72,\qquad
--   \operatorname{cap}_H(P,V\setminus P)\le\psi(P)/12.$$
--
--   There is also a finite program realization that makes exactly two calls, both in $H$, and has at most $C(m+1)$ additional charged work on every tape, uniformly over every correct fair-flow service. Charging either call its actual subroutine cost gives $O(m+T_{fc}(G))$ total time on the connected nontrivial graphs of the source. Empty $P$ and zero deleted capacity remain allowed.
--
--   Differences from the source:
--   - reading: a randomized algorithm, with no machine specified → one finite admissible charged real-RAM program with square roots and independent standard Gaussian and fair-coin tapes; reason: the base machine is the published ClusterDecomp machine; the only new scalar instructions are square root and Gaussian sampling
--   - encoding: finite vertices and nonnegative real capacities → vertices Fin n and loopless edge lists with nonnegative real capacities; parallel entries are retained; reason: the edge list is the input and m is its length; summing parallel entries gives the same cut capacities
--   - generalization: a ψ-expanding graph under the paper’s connectedness convention → the algebraic trace guarantee for any finite graph; the time guarantee still uses connectedness; reason: the proof of the cut and expansion inequalities uses only expansion, not connectedness
--   - encoding: O(m+T_fc(G)) total time using two calls → exactly two ideal calls plus at most C(m+1) ordinary instructions; reason: for connected graphs n≤m+1; replacing either unit call charge by its actual cost recovers the printed bound, while +1 covers constant-size zero-edge inputs
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), p. 37, Theorem 8; algorithm and proof pp. 37–38

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Pruning

namespace SparsestCutOracle.Main

/-- Theorem 8, p.37. Universal two-call correctness and a program realization with O(m) extra work. -/
theorem sparse_prune :
    (∀ (n : ℕ) (G : Graph n) (ψ : Fin n → ℝ) (F : Finset (Fin G.length))
       (U P : Finset (Fin n)) (f₁ f₂ : Flow n),
      G.NoLoops → (∀ v, 0 ≤ ψ v) → ExpandingOn G.toWGraph ψ Finset.univ 1 →
      deletedCapacity G F ≤ totalWeight ψ / 96 →
      SparsePruneTrace G ψ F U f₁ P f₂ → Pruned G ψ F P) ∧
    (∃ P : Procedure, ProcAdmissible P ∧ NoMatvec P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ O : FairService, FairAnswersCorrect O →
      ∀ (n : ℕ) (G : Graph n) (ψ : Fin n → ℝ) (F : Finset (Fin G.length)),
        G.NoLoops → G.Connected → (∀ v, 0 ≤ ψ v) →
        ExpandingOn G.toWGraph ψ Finset.univ 1 → deletedCapacity G F ≤ totalWeight ψ / 96 →
        let s := pruneInput G ψ F
        QueriesInGraph (deleteEdges G F) P O s ∧
        ∀ ω : Tape, ProcHalts P O noMatvec s ω ∧
          let out := procFinal P O noMatvec s ω
          out.fairCalls = 2 ∧
          ((out.machine.base.work - out.fairCalls : ℕ) : ℝ) ≤ C * ((G.length : ℝ) + 1) ∧
          Pruned G ψ F (procCut n out.machine)) := by sorry

end SparsestCutOracle.Main
