-- Prove2me | Theorems.Thm_StrongWeakEq_Discrete_continuity_of_h
-- name    : StrongWeakEq.Discrete.continuity_of_h
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:48.490414+00:00
-- url     : https://prove2.me/theorems/689ad3c8-3501-4922-b13a-0814671ebbf9
-- title:
--   Proof of Theorem 5.1, p. 27 — u ↦ H_j(u) is continuous on 𝒜
-- statement:
--   Assume the standing assumptions of §5: $\mathcal A_i\subseteq\mathfrak P$ for every $i$, each $\kappa(t,i,\cdot)$ is continuous on $\mathfrak P$, and (5.2) holds. Then for every state $j\in S$ the map
--   $$h(u)=\mathbb E_{j,u}\Big[\sum_{t=0}^\infty\kappa(t+1,X_t,u_{X_t})\Big]=H_j(u),\qquad u\in\mathcal A,$$
--   is continuous on $\mathcal A$ (with the topology of $\mathbb R^{N\times N}$).
--
--   Together with (5.4), this gives the joint continuity of $(u',u)\mapsto V(i,u'\otimes_1u)$, which is the regularity the existence proof needs for the best-response correspondence. No convexity or concavity is assumed.
--
--   **Formalization Note** $H_j(u)=\sum_{t\ge0}\sum_k(u^t)_{jk}\kappa(t+1,k,u_k)$ is a `tsum`; continuity is `ContinuousOn` on the set $\mathcal A$ of matrices with rows in $\mathcal A_i$, in the product topology of `Matrix (Fin N) (Fin N) ℝ`. States are `Fin N`.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 27, proof of Theorem 5.1 (Appendix B.1)

import Mathlib
import Definitions.Def_StrongWeakEq_Discrete_DiscreteModel

namespace StrongWeakEq.Discrete

/-- Proof of Theorem 5.1, p. 27: for every `j ∈ S` the map
`h(u) = E_{j,u}[∑_t κ(t+1, X_t, u_{X_t})] = H_j(u)` is continuous on `𝒜`. -/
theorem continuity_of_h {N : ℕ} {A : Fin N → Set (Fin N → ℝ)} {κ : ℕ → Fin N → (Fin N → ℝ) → ℝ}
    (hS : DStanding A κ) (j : Fin N) :
    ContinuousOn (fun u => dH κ u j) (DControls A) := by sorry

end StrongWeakEq.Discrete
