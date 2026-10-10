-- Prove2me | Theorems.Thm_SDDiP_LagCut_validity_base
-- name    : SDDiP.LagCut.validity_base
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:46:34.560177+00:00
-- url     : https://prove2.me/theorems/53d284f9-85a3-4894-be65-9ce68e9f1f0b
-- title:
--   Proof of Theorem 3, last display of p. 479 — Lagrangian cuts are valid at a last-stage node
-- statement:
--   Let $n$ be a last-stage node: it has no children, so its expected cost-to-go is $0$ and $\psi^i_n \equiv 0$; correspondingly the lower bound is $L_n = 0$. Then for every multiplier $\pi \in \mathbb R^d$ and every binary parent state $x_a \in \{0,1\}^d$,
--
--   $$Q_n(x_a) = \min\big\{ f_n(x,y) : (z,x,y) \in X_n,\ z = x_a,\ x \in \{0,1\}^d\big\} \;\ge\; \mathcal L^i_n(\pi) + \pi^\top x_a .$$
--
--   In particular, for an optimal multiplier $\hat\pi$ of (4.3), the Lagrangian cut $(\mathcal L^i_n(\hat\pi), \hat\pi)$ is valid for $Q_n$ in the sense of (3.4). This is the base case of the induction over the stages in the proof of Theorem 3.
--
--   **Formalization Note** The inequality is stated as: $\mathcal L^i_n(\pi) + \pi^\top x_a$ is a lower bound of every objective value $f_n(x,y)$ of a feasible point; when there is none, $Q_n(x_a) = +\infty$ in the paper's convention and the statement is vacuous. The paper uses the optimal multiplier, but its argument and the statement hold for every $\pi$; the Lean statement is the stronger one. The last-stage node is encoded by `nC = 0` and `L = 0`.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 479, proof of Theorem 3, last display

import Mathlib
import Definitions.Def_SDDiP_LagCut_Node

namespace SDDiP.LagCut

open Node

/-- Validity of the Lagrangian cut, base case: proof of Theorem 3, last display of p. 479 (Zou, Ahmed,
Sun, Math. Program. 175 (2019)). At a last-stage node (no children, so no cost-to-go: `ψ^i_n ≡ 0`, here
`L_n = 0`), for every multiplier `π` and every binary parent state `x_a`, every objective value
`f_n(x, y)` of the true nodal problem (2.3) at `x_a` is at least `𝓛^i_n(π) + πᵀx_a`; i.e.
`Q_n(x_a) ≥ 𝓛^i_n(π) + πᵀx_a`. -/
theorem validity_base {d l : ℕ} (N : Node d l) (hleaf : N.nC = 0) (hL : N.L = 0)
    (π xa : Fin d → ℝ) (hxa : IsBinary xa) :
    N.lag π + π ⬝ᵥ xa ∈ lowerBounds (N.trueValues (fun _ => 0) xa) := by sorry

end SDDiP.LagCut
