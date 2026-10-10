-- Prove2me | Theorems.Thm_SDDiP_LagCut_validity_step
-- name    : SDDiP.LagCut.validity_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:46:54.167532+00:00
-- url     : https://prove2.me/theorems/16fdf9b6-d5c6-48ae-a700-24eb8315e5c0
-- title:
--   Proof of Theorem 3, (4.6) and the display after it — valid children's cuts make the Lagrangian cut valid
-- statement:
--   Let $n$ be a node in iteration $i$ with children $m \in \mathcal C(n)$, conditional probabilities $q_{nm} \ge 0$ and children's cut coefficients $(v^\ell_m, \pi^\ell_m)$, $\ell = 1,\dots,i$. Let $Q_m$ be the true value function of child $m$ and $\mathcal Q_n(x) = \sum_m q_{nm} Q_m(x)$. Assume
--
--   1. every child's cut is valid: $Q_m(x) \ge v^\ell_m + (\pi^\ell_m)^\top x$ for all $m$, all $\ell = 1,\dots,i$ and all $x \in \{0,1\}^d$;
--   2. $\mathcal Q_n(x) \ge L_n$ for all $x \in \{0,1\}^d$.
--
--   Then for every multiplier $\pi \in \mathbb R^d$ and every binary parent state $x_a \in \{0,1\}^d$, the true nodal value (2.3), written as in (4.6), satisfies
--
--   $$Q_n(x_a) = \min\big\{ f_n(x,y) + \mathcal Q_n(x) : (z,x,y) \in X_n,\ z = x_a,\ x \in \{0,1\}^d\big\} \;\ge\; \mathcal L^i_n(\pi) + \pi^\top x_a .$$
--
--   With $\pi$ an optimal multiplier of (4.3), this says the Lagrangian cut generated at $n$ is valid (3.4); it is the induction step of the proof of Theorem 3.
--
--   **Formalization Note** As in the base case, the inequality is stated over all feasible points of (2.3), and for every $\pi$ (the paper's argument does not use optimality). Hypothesis 2 is used silently by the paper: $X''_n$ also imposes $\theta \ge L_n$, so it relaxes (4.6) only if $\mathcal Q_n \ge L_n$ ((3.2a) assumes $L_n$ is a lower bound). Hypothesis 1 covers all cuts $\ell = 1,\dots,i$ in $X''_n$, not only those of iteration $i$: the earlier ones are valid by the same theorem at earlier iterations.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 480, proof of Theorem 3, (4.6) and the display after it

import Mathlib
import Definitions.Def_SDDiP_LagCut_Node

namespace SDDiP.LagCut

open Node

/-- Validity of the Lagrangian cut, induction step: proof of Theorem 3, (4.6) and the display after it,
p. 480 (Zou, Ahmed, Sun, Math. Program. 175 (2019)). Let `Qc m` be the true value function `Q_m` of each
child `m` of the node. If every cut of every child is valid, `Q_m(x) ≥ v^ℓ_m + (π^ℓ_m)ᵀx` for all binary
`x`, and the expected cost-to-go `𝒬_n = ∑_m q_{nm} Q_m` dominates `L_n` on binary states, then for every
multiplier `π` and every binary parent state `x_a`, every objective value of the true nodal problem
(2.3)/(4.6) at `x_a` is at least `𝓛^i_n(π) + πᵀx_a`; i.e. `Q_n(x_a) ≥ 𝓛^i_n(π) + πᵀx_a`. -/
theorem validity_step {d l : ℕ} (N : Node d l) (Qc : Fin N.nC → (Fin d → ℝ) → ℝ)
    (hcuts : ∀ (ℓ : Fin N.i) (m : Fin N.nC) (x : Fin d → ℝ), IsBinary x →
      N.v ℓ m + N.π ℓ m ⬝ᵥ x ≤ Qc m x)
    (hL : ∀ x : Fin d → ℝ, IsBinary x → N.L ≤ N.expCostToGo Qc x)
    (π xa : Fin d → ℝ) (hxa : IsBinary xa) :
    N.lag π + π ⬝ᵥ xa ∈ lowerBounds (N.trueValues (N.expCostToGo Qc) xa) := by sorry

end SDDiP.LagCut
