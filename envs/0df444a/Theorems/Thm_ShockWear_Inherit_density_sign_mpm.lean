-- Prove2me | Theorems.Thm_ShockWear_Inherit_density_sign_mpm
-- name    : ShockWear.Inherit.density_sign_mpm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:13.681983+00:00
-- url     : https://prove2.me/theorems/d17b0577-621f-48d3-9153-d3917419d6fb
-- title:
--   Proof of (3.1) — negative–positive–negative sign pattern
-- statement:
--   Let $\lambda>0$, $1=\bar P_0\geq\bar P_1\geq\cdots\geq0$, and $p_{k+1}=\bar P_k-\bar P_{k+1}$. Suppose the sequence $(p_k)_{k\geq1}$ has weakly decreasing successive ratios, with zero terms interpreted through the PF₂ cross-product inequalities. For every $c>0$ and $\theta>0$, the function
--
--   $$t\longmapsto h(t)-ce^{-\theta t},\qquad t>0,$$
--
--   has at most two strict sign changes, in the order negative, positive, negative if two occur. This is the final sign-change claim in the paper's proof of Theorem 3.1(3.1).
--
--   **Formalization Note** A strict positive–negative–positive pattern at three increasing positive times is excluded. Zeros are ignored when counting strict sign changes, as in the paper's variation-diminishing argument.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 633, proof of (3.1), final sign-change claim; https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model

namespace ShockWear.Inherit

/-- The final sign-change assertion in the proof of (3.1), p. 633. -/
theorem density_sign_mpm (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 = 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hpf : IsPF2SeqFrom 1 (failProb P)) :
    ∀ c θ : ℝ, 0 < c → 0 < θ →
      SignMPM (fun t => shockDens lam P t - c * Real.exp (-(θ * t))) (Set.Ioi 0) := by sorry

end ShockWear.Inherit
