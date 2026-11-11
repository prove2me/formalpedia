-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_flow_response
-- name    : SparsestCutOracle.Main.flow_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:40:16.767686+00:00
-- url     : https://prove2.me/theorems/451a2a49-8eb4-4a64-8fa1-f9c36a6995af
-- title:
--   Lemma 4 — Flow response (corrected: added capacity is separate)
-- statement:
--   Write $\Pi=\sum_i\pi(i)$ and $D_\pi=\operatorname{diag}(\pi)$. The matrix $D_F$ is the endpoint-demand Laplacian of the given path flow.
--
--   Let $\widetilde G$ be a supergraph of $G$, and let $F$ be a feasible path flow in $\widetilde G$ whose endpoint load at $i$ is at most $d\pi(i)$. Assume $\pi>0$, $X\succeq0$, $D_\pi\mathbin\bullet X=\Pi$, $\alpha>0$, and $D_F\mathbin\bullet X\ge\alpha$. The explicit response uses the flow's path coefficients, its edge-load Laplacian, $z=0$, and the Laplacian of $\widetilde G$. It meets every algebraic response condition and
--
--   $$b^\top y=\alpha,\qquad Z\mathbin\bullet X\ge0,\qquad
--   -\frac\alpha\Pi D_\pi\preceq Z\preceq2dD_\pi.$$
--
--   The amount of added edge capacity is a separate obligation for callers. The conclusion does not pretend that an arbitrary supergraph has bounded added capacity.
--
--   Differences from the source:
--   - correction: a valid response, including O(αβ) added capacity → the explicit flow response satisfies all algebraic conditions, with no added-capacity assertion; reason: on an even-vertex path with unit capacities and unit weights, let X be the centered ±1 cut Gram matrix at the middle edge, α=8, and double that edge in the supergraph; a feasible two-unit flow gives D_F•X=8 and d=2, but any valid response needs at least one unit of added cut capacity, contradicting Cαβ for β<1/(8C); an unused edge of arbitrary capacity also defeats the printed construction C_out=L(Ĝ)
--   - generalization: the paper’s undirected graph → any symmetric nonnegative finite capacity function, including loops and disconnected graphs; reason: loops contribute zero to the edge and demand Laplacians; the path-flow identities and endpoint bounds use no connectedness, so every source graph is included
--   - encoding: nonnegative path-flow coefficients → finite-support coefficients on all sequences of length at most c_P n; reason: this is the same finite family, with repeats and traversal multiplicities retained
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), p. 20, Lemma 4; Equation (7)

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_SDP

namespace SparsestCutOracle.Main

/-- Lemma 4, p.20 (corrected: arbitrary supergraphs need not have O(αβ) added capacity). -/
theorem flow_response {n cP : ℕ} (G H : ClusterDecomp.WGraph (Fin n))
    (π : Fin n → ℝ) (hπ : ∀ v, 0 < π v) (X : Mat n)
    (hX : X.PosSemidef) (htrace : dot (D π) X = totalWeight π)
    (α d : ℝ) (hα : 0 < α)
    (hsuper : ∀ i j, G.w i j ≤ H.w i j)
    (F : PathFlow n cP) (hF : PathFeasible H F)
    (hbound : BoundedEndpoints π d F) (hgain : α ≤ dot (demandMatrix F) X) :
    let r := flowResponse H F
    AlgebraicResponse G π X α r ∧
    (α / totalWeight π) * totalWeight π = α ∧
    0 ≤ dot (feedback π α r) X ∧
    LePSD (-(α / totalWeight π) • D π) (feedback π α r) ∧
    LePSD (feedback π α r) ((2 * d) • D π) := by sorry

end SparsestCutOracle.Main
