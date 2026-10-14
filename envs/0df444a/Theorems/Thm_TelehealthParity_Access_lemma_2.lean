-- Prove2me | Theorems.Thm_TelehealthParity_Access_lemma_2
-- name    : TelehealthParity.Access.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:13.340297+00:00
-- url     : https://prove2.me/theorems/37ae402f-04ce-4c02-8068-8a1c6e9e1a35
-- title:
--   Lemma 2 — $0<\theta^T<\theta^O<1$ iff $q<1$ and the capacity condition holds
-- statement:
--   Let the parameters satisfy the standing assumptions (2) and (3), let $q>0$ satisfy assumption (6), $0<\kappa(q)\le 1/(1+\sqrt q)^2$, and assume $(1-q)V-c_T>0$. Then the thresholds $\theta^T$ of (11) and $\theta^O$ of (12) satisfy
--   $$0<\theta^T<\theta^O<1 \iff q<1\ \text{ and }\ \frac{h}{\mu}\left(\frac{1}{(1-q)V-c_T}+\frac{1}{V-c_O-\tau}\right)<1.$$
--
--   The lemma guarantees that the four equilibrium regions BO, BOT, BT and B of Figure 3 appear in this order on $[0,1]$.
--
--   **Formalization Note** The hypothesis $(1-q)V-c_T>0$ is not printed in the lemma. The paper's proof presumes it ("θ^T and θ^O are well defined and nonnegative as long as q < 1"), and without it the "if" direction is false (e.g. $V=2.597$, $c_T=0.644$, $c_O=0.193$, $\tau=0.690$, $h/\mu=0.275$, $q=0.976$, where $\theta^T<0$). The condition $q<1$ is kept on the right-hand side as printed, although the added hypothesis implies it.
-- source:
--   Çakıcı and Mills, Telehealth in Acute Care: Pay Parity and Patient Access, SSRN working paper (version of August 19, 2024), p. 14, Lemma 2; proof Appendix C, EC p. 4 (PDF 37)

import Mathlib
import Definitions.Def_TelehealthParity_Access_Setting

namespace TelehealthParity.Access

theorem lemma_2 (p : Params) (hp : p.Standing) (q : ℝ) (hq : 0 < q)
    (hκ : 0 < kappa p q) (hκ' : kappa p q ≤ 1 / (1 + Real.sqrt q) ^ 2)
    (hD : 0 < (1 - q) * p.V - p.cT) :
    (0 < thetaT p q ∧ thetaT p q < thetaO p q ∧ thetaO p q < 1) ↔
      (q < 1 ∧ p.h / p.μ * (1 / ((1 - q) * p.V - p.cT) + 1 / (p.V - p.cO - p.τ)) < 1) := by sorry

end TelehealthParity.Access
