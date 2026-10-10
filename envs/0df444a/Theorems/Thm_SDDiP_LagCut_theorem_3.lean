-- Prove2me | Theorems.Thm_SDDiP_LagCut_theorem_3
-- name    : SDDiP.LagCut.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:46:56.06701+00:00
-- url     : https://prove2.me/theorems/7578126c-d8be-46e2-ac13-00b729287f61
-- title:
--   Theorem 3 — Lagrangian cuts from the local-copy reformulation are valid and tight at binary states
-- statement:
--   Let $n$ be a node of the scenario tree in the backward step of iteration $i$ of SND/SDDiP, with nodal constraint set $X_n$ (nonempty, compact, mixed integer polyhedral), linear objective $f_n$, lower bound $L_n$, children $m$ with probabilities $q_{nm} \ge 0$ and children's cuts $(v^\ell_m, \pi^\ell_m)$, $\ell = 1,\dots,i$, and assume $X''_n \ne \emptyset$. Let $\hat x \in \{0,1\}^d$ be the binary forward-step state of the parent, let $\hat\pi$ be an optimal solution of the Lagrangian dual (4.3)
--   $$(R^i_n):\quad \max_{\pi\in\mathbb R^d}\ \big\{\mathcal L^i_n(\pi) + \pi^\top \hat x\big\},$$
--   and let $\hat v = \mathcal L^i_n(\hat\pi)$. Then the Lagrangian cut $(\hat v, \hat\pi)$ is
--
--   1. **tight** (3.5): $\hat v + \hat\pi^\top\hat x = \underline Q^i_n(\hat x, \psi^{i+1}_n)$, the (attained) optimal value of the updated forward problem (3.1);
--   2. **valid** (3.4): if the children's cuts are valid for their true value functions $Q_m$, i.e. $Q_m(x) \ge v^\ell_m + (\pi^\ell_m)^\top x$ for all $m$, $\ell$ and $x \in \{0,1\}^d$, and $\mathcal Q_n = \sum_m q_{nm}Q_m \ge L_n$ on $\{0,1\}^d$, then
--   $$Q_n(x_a) \ge \hat v + \hat\pi^\top x_a \qquad \text{for every } x_a \in \{0,1\}^d,$$
--   where $Q_n$ is the true value function (2.3) of the node.
--
--   This is the main result of §4.3: Lagrangian cuts obtained by dualizing the copy constraint $z_n = x_{a(n)}$ of the reformulation (2.1) satisfy the validity and tightness conditions of Definition 2, so SND and SDDiP with these cuts (made finite by choosing basic dual solutions) converge to an optimal solution of a multistage stochastic integer program with binary states.
--
--   **Formalization Note** The paper states Theorem 3 for the whole collection $\{(v^i_n,\pi^i_n)\}_{n\in\Omega^i}$ and proves validity by induction over the stages. The Lean statement is the node statement that carries out both the base case and the induction step: the validity hypotheses on the children are the induction hypothesis, and at a last-stage node (no children, $L_n = 0$) they hold trivially. The paper's sentence follows by applying it at every sampled node, from the last stage backwards. "$Q_n(x_a) \ge \dots$" is stated over all feasible points of (2.3) (the minimum is $+\infty$ when there are none). The hypothesis $X''_n \ne \emptyset$ makes $\mathcal L^i_n$ a genuine minimum, as the paper writes it.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 479, Theorem 3

import Mathlib
import Definitions.Def_SDDiP_LagCut_Node

namespace SDDiP.LagCut

open Node

/-- Theorem 3, Zou, Ahmed, Sun, *Stochastic dual dynamic integer programming*, Math. Program. 175 (2019),
p. 479, stated at one node `n`. Let `x̂ ∈ {0,1}ᵈ` be the binary forward-step state of the parent, let
`π̂` be an optimal solution of the Lagrangian dual (4.3) and `v̂ = 𝓛^i_n(π̂)`. Then the Lagrangian cut
`(v̂, π̂)` is

* **tight** (3.5): `v̂ + π̂ᵀx̂` is the (attained) optimal value `Q̲^i_n(x̂, ψ^{i+1}_n)` of (3.1);
* **valid** (3.4): if the cuts of the children are valid for their true value functions `Q_m` and
  `𝒬_n = ∑_m q_{nm} Q_m ≥ L_n` on binary states (the induction hypothesis of the proof), then
  `Q_n(x_a) ≥ v̂ + π̂ᵀx_a` for every binary `x_a`, `Q_n` the true value function (2.3).

The paper's statement about the whole collection follows by induction over the stages, which this node
statement carries out (a last-stage node has no children, and then `L_n = 0` meets the hypothesis). -/
theorem theorem_3 {d l : ℕ} (N : Node d l) (xhat : Fin d → ℝ) (hxhat : IsBinary xhat)
    (hX' : N.X'.Nonempty) (πhat : Fin d → ℝ) (hopt : N.IsDualOptimal xhat πhat)
    (Qc : Fin N.nC → (Fin d → ℝ) → ℝ)
    (hcuts : ∀ (ℓ : Fin N.i) (m : Fin N.nC) (x : Fin d → ℝ), IsBinary x →
      N.v ℓ m + N.π ℓ m ⬝ᵥ x ≤ Qc m x)
    (hL : ∀ x : Fin d → ℝ, IsBinary x → N.L ≤ N.expCostToGo Qc x) :
    (IsLeast (N.fwdValues xhat) (N.lag πhat + πhat ⬝ᵥ xhat) ∧
        N.fwdValue xhat = N.lag πhat + πhat ⬝ᵥ xhat) ∧
      ∀ xa : Fin d → ℝ, IsBinary xa →
        N.lag πhat + πhat ⬝ᵥ xa ∈ lowerBounds (N.trueValues (N.expCostToGo Qc) xa) := by sorry

end SDDiP.LagCut
