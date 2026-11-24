-- Prove2me | Theorems.Thm_SensitivityProfileCycle_scaled_radius_lower
-- name    : SensitivityProfileCycle.scaled_radius_lower
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-24T09:02:36.909386+00:00
-- url     : https://prove2.me/theorems/3559fa37-235a-4ae9-92fc-f97a9861b5b3
-- title:
--   A uniform lower bound on the return factor of a profile cycle
-- statement:
--   Let a profile cycle have vertex count $K$, regular outdegree $d$, period $L$, and return factor $R$. For every nonnegative integer scale $s$, put $$B=\min\{sK,2s(d+1),s(d+2)+\lfloor\sqrt{8ds^2}\rfloor\}.$$ Then $B^L\le s^L R^2$. The same inequality applies to every choice of tolerances, cutoffs, recipes, and profiles allowed by the certificate.
-- source:
--   The certificate and its step inequalities are defined at https://prove2.me/definitions/6f70ee20-3318-4365-9377-022df0d68b3f . This is a new uniform generalization of the diagonal-product obstruction at fixed K = 14055 and q ≤ 5, whose proof selects n = m = u = 1 in the ordinary costs. https://prove2.me/submissions/4b7c1dc7-bec0-4175-ad6c-0b721c44a55d

import Definitions.Def_SensitivityProfileCycle

theorem SensitivityProfileCycle.scaled_radius_lower (C : SensitivityProfileCycle.Certificate) (s : ℕ) :
    (min (s*C.vertices) (min (2*s*(C.degree+1))
      (s*(C.degree+2)+Nat.sqrt (8*C.degree*s^2)))) ^ C.period ≤
      s ^ C.period * C.radius^2 := by sorry
