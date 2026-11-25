-- Prove2me | Theorems.Thm_SSLWithoutPairs_predictor_fixed_point_symmetric
-- name    : SSLWithoutPairs.predictor_fixed_point_symmetric
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T06:39:51.228165+00:00
-- url     : https://prove2.me/theorems/9f8243ec-b463-412e-97d6-48b32175ff06
-- title:
--   Section 3: the fixed point of eq. (2) under Assumptions 1 and 2 with $\eta>0$ is symmetric
-- statement:
--   Under Assumptions 1 and 2 ($W_a=\tau W$, $X=I$, $X'=\sigma^2I$), write $F=WW^\top$. The predictor flow (2) becomes $\dot W_p=-\alpha_p(1+\sigma^2)W_pF+\alpha_p\tau F-\eta W_p$. Let $\alpha_p>0$ and $\eta>0$. If $W_p$ is a fixed point,
--
--   $$-\alpha_p(1+\sigma^2)W_pF+\alpha_p\tau F-\eta W_p=0,$$
--
--   then $W_p$ is symmetric.
--
--   This motivates Assumption 3 (symmetric predictor). For $\eta=0$ the fixed point need not be unique or symmetric.
-- source:
--   Tian, Chen and Ganguli, Understanding Self-Supervised Learning Dynamics without Contrastive Pairs, arXiv:2102.06810v4 (2021), Section 3, discussion of Assumption 3, p. 4; derivation in Appendix B, eqs. (62)-(66), pp. 15-16

import Mathlib
import Definitions.Def_SSLWithoutPairs_Basic

open MeasureTheory ProbabilityTheory Filter Topology Matrix

namespace SSLWithoutPairs

theorem predictor_fixed_point_symmetric {d n₁ : ℕ} (αp σ η τ : ℝ) (hαp : 0 < αp) (hη : 0 < η)
    (W : Matrix (Fin d) (Fin n₁) ℝ) (Wp : Matrix (Fin d) (Fin d) ℝ)
    (hfix : isoFlowWp αp σ η τ Wp (W * Wᵀ) = 0) :
    Wpᵀ = Wp := by sorry

end SSLWithoutPairs
