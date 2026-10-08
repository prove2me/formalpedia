-- Prove2me | Theorems.Thm_ProgHedging_Convex_theorem_5_1
-- name    : ProgHedging.Convex.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:26:39.942001+00:00
-- url     : https://prove2.me/theorems/3d1e24a1-4b41-4049-a6c7-672d00b33a4f
-- title:
--   Theorem 5.1 — convex progressive hedging is bounded iff (P) and (D) have solutions, and then converges to such a pair, monotonically in ‖·‖_r
-- statement:
--   Consider the progressive hedging algorithm in the convex case with exact minimization and a fixed $r>0$, started from an arbitrary policy $X^0$ and a price system $W^0\in\mathcal M$, and let $\hat X^\nu=JX^\nu$ and $W^\nu$ be the sequences it generates. Then:
--
--   1. the sequences $\{\hat X^\nu\}$ and $\{W^\nu\}$ are bounded if and only if (P) and (D) both have optimal solutions;
--   2. in that case there is a particular pair $X^*$ optimal for (P) and $W^*$ optimal for (D) such that
--   $$
--   \hat X^\nu\to X^*,\qquad W^\nu\to W^*,
--   $$
--   and, in terms of $\|(X,W)\|_r=(\|X\|^2+r^{-2}\|W\|^2)^{1/2}$, for every $\nu=0,1,2,\dots$
--   $$
--   \|(\hat X^{\nu+1},W^{\nu+1})-(X^*,W^*)\|_r\le\|(\hat X^\nu,W^\nu)-(X^*,W^*)\|_r,
--   $$
--   with strict inequality unless $(\hat X^\nu,W^\nu)=(X^*,W^*)$, while for every $\nu=1,2,\dots$
--   $$
--   \|(\hat X^{\nu+1},W^{\nu+1})-(\hat X^\nu,W^\nu)\|_r\le\|(\hat X^\nu,W^\nu)-(\hat X^{\nu-1},W^{\nu-1})\|_r .
--   $$
--
--   This is the main convergence theorem for progressive hedging: every iteration strictly improves the distance to a primal–dual solution until one is reached, and boundedness of the iterates detects solvability.
--
--   **Formalization Note.** Boundedness and convergence of policy sequences use Mathlib's topology on `S → EuclideanSpace ℝ (Fin n)`, which in finite dimension agrees with that of the norm $\|X\|=\langle X,X\rangle^{1/2}$; the inequalities use $\|\cdot\|_r$ built from that weighted norm, never Mathlib's sup norm. The paper adds "i.e. there exist $X^*$ and $W^*$ satisfying the optimality conditions in Theorem 4.1, or equivalently the saddle point condition in Theorem 4.2"; that equivalence is the content of Theorems 4.2 and 4.6, and the theorem is stated with the printed condition, existence of optimal solutions of (P) and (D).
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), pp. 20–21, Theorem 5.1, (5.1)–(5.4)

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Convex_Duality
import Definitions.Def_ProgHedging_Convex_Algorithm
open scoped RealInnerProductSpace Pointwise Topology
open Filter

namespace ProgHedging.Convex

/-- Theorem 5.1, pp. 20–21. Progressive hedging in the convex case with exact minimization, from
arbitrary `X⁰` and `W⁰ ∈ ℳ`: the sequences `X̂^ν = J X^ν` and `W^ν` are bounded iff (P) and (D) both
have optimal solutions. In that case they converge to some optimal pair `(X*, W*)`, the distance to
it in `‖·‖_r` (5.2) does not increase (5.3), strictly unless `(X̂^ν, W^ν) = (X*, W*)`, and the step
lengths in `‖·‖_r` do not increase from `ν = 1` on (5.4). -/
theorem theorem_5_1 {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (hconv : pr.ConvexCase) {r : ℝ} (hr : 0 < r)
    (X W : ℕ → Policy S n) (hseq : pr.IsExactPHSeq r X W) :
    ((Bornology.IsBounded (Set.range fun ν => pr.J (X ν)) ∧ Bornology.IsBounded (Set.range W)) ↔
        ((∃ Xs, pr.SolvesP Xs) ∧ ∃ Ws, pr.SolvesD Ws)) ∧
    (((∃ Xs, pr.SolvesP Xs) ∧ ∃ Ws, pr.SolvesD Ws) →
      ∃ Xs Ws, pr.SolvesP Xs ∧ pr.SolvesD Ws ∧
        Tendsto (fun ν => pr.J (X ν)) atTop (𝓝 Xs) ∧ Tendsto W atTop (𝓝 Ws) ∧
        (∀ ν, pr.rnorm r (pr.J (X (ν + 1)) - Xs) (W (ν + 1) - Ws) ≤
              pr.rnorm r (pr.J (X ν) - Xs) (W ν - Ws) ∧
          ((pr.J (X ν), W ν) ≠ (Xs, Ws) →
            pr.rnorm r (pr.J (X (ν + 1)) - Xs) (W (ν + 1) - Ws) <
              pr.rnorm r (pr.J (X ν) - Xs) (W ν - Ws))) ∧
        ∀ ν, 1 ≤ ν →
          pr.rnorm r (pr.J (X (ν + 1)) - pr.J (X ν)) (W (ν + 1) - W ν) ≤
            pr.rnorm r (pr.J (X ν) - pr.J (X (ν - 1))) (W ν - W (ν - 1))) := by sorry

end ProgHedging.Convex
