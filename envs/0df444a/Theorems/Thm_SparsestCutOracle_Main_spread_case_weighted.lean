-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_spread_case_weighted
-- name    : SparsestCutOracle.Main.spread_case_weighted
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:43:21.733385+00:00
-- url     : https://prove2.me/theorems/bd3bf6cc-17d5-49ae-bb38-56b0f086c0f6
-- title:
--   Lemma 7 — Weighted uniformly spread vectors
-- statement:
--   Let $C$ be the input graph Laplacian, $\Pi=\sum_i\pi(i)$ and $D_\pi=\operatorname{diag}(\pi)$. The admissible range is $c_1/\log n\le\kappa\le c_2$, and $T_p$ denotes the path-inequality matrix for a sequence of length at most $c_Pn$.
--
--   Fix $\xi,R>0$. Let $\pi\ge0$, $\Pi>0$, and let $X_W$ be a Gram matrix. Assume $\pi(A)\ge\Pi/2$, $(X_W)_{ii}\le R^2$ on $A$, and weighted ordered-pair spread at least $\xi\Pi^2$. For all admissible $\kappa$ and every $\alpha>0$, a finite oracle-relative program returns with high probability either nonnegative path multipliers and a Laplacian $F\preceq C$ with
--
--   $$Q=\sum_p f_pT_p-F,\quad Q\mathbin\bullet X_W\le-\alpha,\quad
--   -\rho D_\pi\preceq Q\preceq\rho D_\pi,\qquad\rho=C_w(\alpha/\Pi)(\log n)^2,$$
--
--   or a cut of weight between $b\Pi$ and its complement's weight and capacity at most $C_q(\alpha/\Pi)\sqrt{\log n/\kappa}\,\pi(S)$. It uses an expected $C_{\mathrm{calls}} n^\kappa(\log n)^c$ 2-fair calls in graphs with $\Theta(n)$ vertices and $O(m)$ edges. Constants are fixed after $\xi,R$ and before all instances; zero weights remain allowed.
--
--   Differences from the source:
--   - reading: a randomized algorithm, with no machine specified → one finite admissible charged real-RAM program with square roots and independent standard Gaussian and fair-coin tapes; reason: the base machine is the published ClusterDecomp machine; the only new scalar instructions are square root and Gaussian sampling
--   - reading: with high probability → for every natural exponent a, a measurable event of probability at least 1 − n^(−a); reason: the program and time constants may depend on a; qualitative approximation constants precede a
--   - encoding: finite vertices and nonnegative real capacities → vertices Fin n and loopless edge lists with nonnegative real capacities; parallel entries are retained; reason: the edge list is the input and m is its length; summing parallel entries gives the same cut capacities
--   - encoding: calls to FairCutFlow → a finite oracle-relative program, uniformly over every correct measurable fair-flow service, with explicit expected call count and graph-size bounds; reason: the query-only ideal service models valid subroutine outputs; measurability is the standing convention for a randomized procedure; no arbitrary function is a program instruction; raw query endpoints, capacities, counts and demands must already be well formed, so parsing performs no free repair
--   - encoding: linear-length sequences P_n → a positive integer c_P chosen after ξ,R and before the instance; reason: the constructed reduction has z≤(1+64R²/ξ)n vertices, and this is the source’s later choice of the sequence-length constant
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), pp. 24–25, Lemma 7; proof pp. 34–36

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Geometry

namespace SparsestCutOracle.Main

/-- Lemma 7, pp.24–25. Constants are uniform after fixing ξ,R; zero weights remain allowed. -/
theorem spread_case_weighted (ξ R : ℝ) (hξ : 0 < ξ) (hR : 0 < R) :
    ∃ c₁ c₂ b Cq Cwidth Csize : ℝ, ∃ cP : ℕ,
      0 < c₁ ∧ 0 < c₂ ∧ 0 < b ∧ 0 < Cq ∧ 0 < Cwidth ∧ 1 ≤ Csize ∧ 1 ≤ cP ∧
      ∀ a : ℕ, ∃ P : Procedure, ProcAdmissible P ∧ NoMatvec P ∧
        ∃ c : ℕ, ∃ Ccalls : ℝ, 0 < Ccalls ∧
        ∀ O : FairService, ValidFairService O →
        ∀ (n : ℕ) (G : Graph n) (π : Fin n → ℝ) (X : Mat n)
          (A : Finset (Fin n)) (κ α : ℝ),
          2 ≤ n → G.NoLoops → G.Connected → (∀ v, 0 ≤ π v) → 0 < totalWeight π →
          X.PosSemidef → totalWeight π / 2 ≤ mass π A →
          (∀ i ∈ A, X i i ≤ R ^ 2) → ξ * totalWeight π ^ 2 ≤ spread π X A →
          c₁ / Real.log n ≤ κ → κ ≤ c₂ → 0 < α →
          let s := oracleInput G π X [ξ, R, κ, α] A
          QuerySizes P O s ((n : ℝ) / Csize) (Csize * n) 0 (Csize * G.length) ∧
          ExpectedCalls P O s (Ccalls * (n : ℝ) ^ κ * Real.log n ^ c) ∧
          ProcHighProbability n a P O noMatvec s
            (fun out => SpreadOutcome (cP := cP) G π X α κ b Cq Cwidth out.machine) := by sorry

end SparsestCutOracle.Main
