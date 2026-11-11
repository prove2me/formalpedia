-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_balsep_unweighted
-- name    : SparsestCutOracle.Main.balsep_unweighted
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:44:09.20621+00:00
-- url     : https://prove2.me/theorems/5a8b978f-19f7-430d-8f26-9dd077ae90f5
-- title:
--   Lemma 11 — Unweighted BalSep with fair flows
-- statement:
--   Let $G=(V,E)$ be the connected graph on $n\ge2$ vertices, with Laplacian $C$. Write $d_X(i,j)=X_{ii}+X_{jj}-2X_{ij}$ for squared Gram distances. The admissible range is $c_1/\log n\le\kappa\le c_2$.
--
--   Fix $\xi>0$. Let $X$ be a Gram matrix and let $A\subseteq V$ satisfy $|A|\ge n/2$, $X_{ii}\le2$ for $i\in A$, and $\sum_{i,j\in A}d_X(i,j)\ge\xi n^2$. Constants depend only on $\xi$. In the admissible range of $\kappa$, for every $\alpha>0$, a finite program uses an expected $C_{\mathrm{calls}} n^\kappa(\log n)^c$ fair-flow calls in the original graph and, with high probability, returns either a cut with
--
--   $$bn\le\min\{|S\cap A|,|A\setminus S|\},\qquad
--   \operatorname{cap}(S,V\setminus S)\le C_q\frac\alpha n\sqrt{\log n/\kappa}\,|S\cap A|,$$
--
--   or a Laplacian $F\preceq C$ and nonnegative multipliers supported only on distinct-vertex sequences such that $Q=\sum_p f_pT_p-F$ is supported on $A\times A$, $Q\mathbin\bullet X\le-\alpha$, and $\|Q\|_2\le C_w(\alpha/n)(\log n)^2$. Every response clause and both cut clauses are retained.
--
--   Differences from the source:
--   - reading: a randomized algorithm, with no machine specified → one finite admissible charged real-RAM program with square roots and independent standard Gaussian and fair-coin tapes; reason: the base machine is the published ClusterDecomp machine; the only new scalar instructions are square root and Gaussian sampling
--   - reading: with high probability → for every natural exponent a, a measurable event of probability at least 1 − n^(−a); reason: the program and time constants may depend on a; qualitative approximation constants precede a
--   - encoding: finite vertices and nonnegative real capacities → vertices Fin n and loopless edge lists with nonnegative real capacities; parallel entries are retained; reason: the edge list is the input and m is its length; summing parallel entries gives the same cut capacities
--   - encoding: calls to FairCutFlow → a finite oracle-relative program, uniformly over every correct measurable fair-flow service, with explicit expected call count and graph-size bounds; reason: the query-only ideal service models valid subroutine outputs; measurability is the standing convention for a randomized procedure; no arbitrary function is a program instruction; raw query endpoints, capacities, counts and demands must already be well formed, so parsing performs no free repair
--   - encoding: spectral norm bound and distinct sequences in P_n → two Loewner inequalities against the identity and sequences of length at most n; reason: for symmetric Q these are equivalent to the spectral bound; distinct sequences have length at most n
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), p. 27, Lemma 11; pp. 28–31

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Geometry

namespace SparsestCutOracle.Main

/-- Lemma 11, p.27. Its three response clauses, both cut clauses, expected calls, and success probability. -/
theorem balsep_unweighted (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ c₁ c₂ b Cq Cwidth : ℝ,
      0 < c₁ ∧ 0 < c₂ ∧ 0 < b ∧ 0 < Cq ∧ 0 < Cwidth ∧
      ∀ a : ℕ, ∃ P : Procedure, ProcAdmissible P ∧ NoMatvec P ∧
        ∃ c : ℕ, ∃ Ccalls : ℝ, 0 < Ccalls ∧
        ∀ O : FairService, ValidFairService O →
        ∀ (n : ℕ) (G : Graph n) (X : Mat n) (A : Finset (Fin n)) (κ α : ℝ),
          2 ≤ n → G.NoLoops → G.Connected → X.PosSemidef →
          (n : ℝ) / 2 ≤ A.card → (∀ i ∈ A, X i i ≤ 2) →
          ξ * (n : ℝ) ^ 2 ≤ spread (fun _ => 1) X A →
          c₁ / Real.log n ≤ κ → κ ≤ c₂ → 0 < α →
          let s := oracleInput G (fun _ => 1) X [ξ, κ, α] A
          QueriesInGraph G P O s ∧
          ExpectedCalls P O s (Ccalls * (n : ℝ) ^ κ * Real.log n ^ c) ∧
          ProcHighProbability n a P O noMatvec s
            (fun out => UnweightedOutcome (cP := 1) G X A α κ b Cq Cwidth out.machine) := by sorry

end SparsestCutOracle.Main
