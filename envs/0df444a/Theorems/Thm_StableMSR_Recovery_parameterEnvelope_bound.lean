-- Prove2me | Theorems.Thm_StableMSR_Recovery_parameterEnvelope_bound
-- name    : StableMSR.Recovery.parameterEnvelope_bound
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T14:30:46.205563+00:00
-- url     : https://prove2.me/theorems/c61deb04-6819-4d67-bda4-35d12d42efe9
-- title:
--   Table 2 parameter envelope has a uniform inverse-fifth bound
-- statement:
--   Let $0<\varepsilon<1$, and let $N_\varepsilon,F_\varepsilon,h_\varepsilon,\omega_\varepsilon$ be the exact integer parameters of Table 2, with the ceilings and floor specified there. Define the running-time envelope
--   $$E(\varepsilon)=N_\varepsilon+F_\varepsilon+h_\varepsilon(\omega_\varepsilon+1)+1.$$
--   There is an absolute real constant $K>0$, independent of $\varepsilon$, such that
--   $$E(\varepsilon)\le K/\varepsilon^5\qquad(0<\varepsilon<1).$$
--   This numerical statement makes the inverse-fifth exponent in Appendix A.5 explicit. It concerns the parameter bound only; it does not assert that a recovery program has been constructed.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547v1, https://arxiv.org/html/2611.03547v1, Table 2; Appendix A.2 (parameters); Appendix A.5 (total running-time exponent).

import Definitions.Def_StableMSR_Recovery_Parameters

set_option autoImplicit false

namespace StableMSR.Recovery

theorem parameterEnvelope_bound : ∃ K : ℝ, 0 < K ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 → (parameterEnvelope ε : ℝ) ≤ K / ε ^ 5 := by sorry

end StableMSR.Recovery
