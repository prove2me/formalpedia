-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_dense_region_case
-- name    : SparsestCutOracle.Main.dense_region_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:43:25.005206+00:00
-- url     : https://prove2.me/theorems/f1d517d7-7787-46ea-8f90-4f2e59a2de9e
-- title:
--   Lemma 5 — Dense-region oracle case
-- statement:
--   Let $G=(V,E)$ be the connected input graph on $n\ge2$ vertices. Write $\Pi=\sum_i\pi(i)$, $D_\pi=\operatorname{diag}(\pi)$, $J_\pi=\pi\pi^\top$, $K_\pi=\Pi D_\pi-J_\pi$, and $r_0=1/(2\sqrt{10})$. Balls use Euclidean distances determined by the Gram matrix.
--
--   Suppose $X\succeq0$, $D_\pi\mathbin\bullet X=\Pi$, $\pi>0$, and
--
--   $$\frac45\Pi^2\le K_\pi\mathbin\bullet X\le\Pi^2,\qquad
--   \pi(B(i_0,2r_0))\ge\Pi/4.$$
--
--   In the standing admissible range of $\kappa$ and for $\alpha>0$, $0<\beta\le1/12$, a finite program using at most one ideal 2-fair call in $G$ terminates for every tape and every valid subroutine output. It returns either a valid response with width $C_w\alpha/\Pi$ and at most $C_e\alpha\beta$ added capacity, or a cut satisfying
--
--   $$\beta\Pi\le\pi(S)\le\pi(V\setminus S),\qquad
--   \operatorname{cap}(S,V\setminus S)\le C_q\frac\alpha\Pi\sqrt{\log n/\kappa}\,\pi(S).$$
--
--   All constants precede the instance. This is the complete dense-region alternative, including its subroutine realization.
--
--   Differences from the source:
--   - reading: a randomized algorithm, with no machine specified → one finite admissible charged real-RAM program with square roots and independent standard Gaussian and fair-coin tapes; reason: the base machine is the published ClusterDecomp machine; the only new scalar instructions are square root and Gaussian sampling
--   - encoding: finite vertices and nonnegative real capacities → vertices Fin n and loopless edge lists with nonnegative real capacities; parallel entries are retained; reason: the edge list is the input and m is its length; summing parallel entries gives the same cut capacities
--   - encoding: the Case B procedure and the standing κ-range of §4.3 → one oracle-relative program, at most one fair call, and explicit c₁/log n ≤ κ ≤ c₂; reason: the proof uses one call; including the standing upper κ bound is necessary for Equation (6)
--   - encoding: O(α/Π) width and O(αβ) added capacity → positive constants C_w,C_e,C_q fixed before the instance; reason: the proof gives, for example, at most 10αβ added capacity; constants are not selected after seeing G
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), p. 22, Lemma 5; pp. 19, 23–24; Equation (6)

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Geometry

namespace SparsestCutOracle.Main

/-- Lemma 5, p.22. A charged program, universally over every valid output of its one fair-flow call. -/
theorem dense_region_case :
    ∃ c₁ c₂ Cq Cadd Cwidth : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      0 < Cq ∧ 0 < Cadd ∧ 0 < Cwidth ∧
      ∀ cP : ℕ, 1 ≤ cP → ∃ P : Procedure, ProcAdmissible P ∧ NoMatvec P ∧
        ∀ (O : FairService), FairAnswersCorrect O →
        ∀ (n : ℕ) (G : Graph n) (π : Fin n → ℝ) (X : Mat n)
          (α β κ : ℝ) (i₀ : Fin n),
          2 ≤ n → G.NoLoops → G.Connected → (∀ v, 0 < π v) → X.PosSemidef →
          dot (D π) X = totalWeight π → 0 < α → 0 < β → β ≤ (1 / 12 : ℝ) →
          c₁ / Real.log n ≤ κ → κ ≤ c₂ →
          (4 / 5 : ℝ) * totalWeight π ^ 2 ≤ dot (K π) X →
          dot (K π) X ≤ totalWeight π ^ 2 →
          totalWeight π / 4 ≤ mass π (ball X i₀ (2 * r₀)) →
          let s := oracleInput G π X [α, β, κ, (i₀.val : ℝ)]
          QueriesInGraph G P O s ∧
          ∀ ω : Tape, ProcHalts P O noMatvec s ω ∧
            (procFinal P O noMatvec s ω).fairCalls ≤ 1 ∧
            DenseOutcome (cP := cP) G π X α β κ Cq Cadd Cwidth
              (procFinal P O noMatvec s ω).machine := by sorry

end SparsestCutOracle.Main
