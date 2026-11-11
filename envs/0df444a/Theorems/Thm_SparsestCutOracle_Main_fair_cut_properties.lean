-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_fair_cut_properties
-- name    : SparsestCutOracle.Main.fair_cut_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:04.096287+00:00
-- url     : https://prove2.me/theorems/d0513457-5a4f-4ad9-bda1-bf57aba2f794
-- title:
--   Claim 1 — Four inequalities for a fair cut
-- statement:
--   Let $(U,f)$ be an $\omega$-fair cut/flow pair for nonnegative vertex weights $s,t$. Then
--
--   $$\begin{aligned}
--   \operatorname{cap}(U,\bar U)+t(U)&\le\omega s(U),\\
--   \operatorname{cap}(U,\bar U)+s(\bar U)&\le\omega t(\bar U),\\
--   \operatorname{cap}(A,\bar U)+t(A)&\le\omega(s(A)+\operatorname{cap}(A,U\setminus A))&& (A\subseteq U),\\
--   \operatorname{cap}(B,U)+s(B)&\le\omega(t(B)+\operatorname{cap}(B,\bar U\setminus B))&& (B\subseteq\bar U).
--   \end{aligned}$$
--
--   Here $\bar U=V\setminus U$ and weights are summed over sets. Both global and both local inequalities are retained. They supply the quantitative interface used in the dense-region and pruning arguments.
--
--   Differences from the source:
--   - generalization: the paper’s undirected graph → any symmetric nonnegative finite capacity function, including loops and disconnected graphs; reason: loops contribute zero to cuts and antisymmetry forces zero diagonal flow; the algebraic statement includes every source graph
--   - encoding: a finite vertex set → Fin n, with no nonemptiness restriction on this algebraic statement; reason: the inequalities also hold for empty and singleton sets
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), pp. 9–10, Claim 1 (Lemma 7 in [HMR26])

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_FairFlow

namespace SparsestCutOracle.Main

/-- Claim 1 (Lemma 7 in [HMR26]), pp.9–10, including both local inequalities. -/
theorem fair_cut_properties {n : ℕ} (G : ClusterDecomp.WGraph (Fin n))
    (s t : Fin n → ℝ) (ω : ℝ) (U : Finset (Fin n))
    (h : FairCut G s t ω U) :
    cut G U Uᶜ + mass t U ≤ ω * mass s U ∧
    cut G U Uᶜ + mass s Uᶜ ≤ ω * mass t Uᶜ ∧
    (∀ A : Finset (Fin n), A ⊆ U →
      cut G A Uᶜ + mass t A ≤ ω * (mass s A + cut G A (U \ A))) ∧
    (∀ B : Finset (Fin n), B ⊆ Uᶜ →
      cut G B U + mass s B ≤ ω * (mass t B + cut G B (Uᶜ \ B))) := by sorry

end SparsestCutOracle.Main
