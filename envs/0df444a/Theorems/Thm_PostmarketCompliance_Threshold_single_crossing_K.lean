-- Prove2me | Theorems.Thm_PostmarketCompliance_Threshold_single_crossing_K
-- name    : PostmarketCompliance.Threshold.single_crossing_K
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:12.363637+00:00
-- url     : https://prove2.me/theorems/c3ae4c14-af2d-4f9c-8066-f19c7386167d
-- title:
--   Proof of Proposition 1 — one crossing of the deadline kernel
-- statement:
--   For positive effort $\lambda$, define
--
--   $$
--   K(t)=-\pi_A G(t,\lambda,n)+(T-t)\alpha\pi_R g(t,\lambda,n).
--   $$
--
--   There is exactly one $t_0\in(0,T)$ at which the sign changes: $K(t)>0$ for $0<t<t_0$, and $K(t)<0$ for $t_0<t\le T$. This crossing controls the direction of the deadline comparison in the paper’s proof of Proposition 1.
--
--   **Formalization Note** The paper prints $K(0)>0$, but $K(0)=0$ for the standing regime $n\ge2$. The statement uses the open interval at zero and applies to every positive $\lambda$, including the paper’s optimal $\bar\lambda$.
-- source:
--   Xu, Zhao & Petruzzi, Inducing Compliance with Post-Market Studies for Drugs under FDA's Accelerated Approval Pathway, SSRN 3471632 (version of March 2019), p. 38 (PDF 39), proof of Proposition 1

import Mathlib
import Definitions.Def_PostmarketCompliance_Threshold_Model

namespace PostmarketCompliance.Threshold

theorem single_crossing_K (P : Params) (hP : P.Standing) (lam : ℝ)
    (hlam : 0 < lam) :
    ∃ t₀ ∈ Set.Ioo (0 : ℝ) P.T,
      (∀ t ∈ Set.Ioo (0 : ℝ) t₀, 0 < K P lam t) ∧
      (∀ t ∈ Set.Ioc t₀ P.T, K P lam t < 0) := by sorry

end PostmarketCompliance.Threshold
