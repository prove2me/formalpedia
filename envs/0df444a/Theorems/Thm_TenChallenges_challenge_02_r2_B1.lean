-- Prove2me | Theorems.Thm_TenChallenges_challenge_02_r2_B1
-- name    : TenChallenges.challenge_02_r2_B1
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-04T21:55:19.772408+00:00
-- url     : https://prove2.me/theorems/ca5aeeca-8fa8-4e26-acaa-48b7f08eb476
-- title:
--   Tutte: one excluded minor for $\mathrm{GF}(2)$
-- statement:
--   **Tutte's excluded-minor theorem**, as the rung $S(2,1)$ of Challenge 2:
--
--   $$\text{the class of binary matroids has at most one excluded minor up to isomorphism.}$$
--
--   Here binary means $\mathrm{GF}(2)$-representable, and the prime power $2$ is the only one not exceeding $r=2$. The excluded minor is the uniform matroid $U_{2,4}$; the statement asserts only the bound on the number of isomorphism classes, not the identity of the excluded minor.
-- source:
--   W. T. Tutte, A homotopy theorem for matroids, I, II, Trans. AMS 88 (1958), 144–174, https://doi.org/10.1090/S0002-9947-1958-0101526-0; stated as Theorem 6.5.4 in J. Oxley, Matroid Theory, 2nd ed.

import Definitions.Def_TenChallenges_Challenge_02

namespace TenChallenges
theorem challenge_02_r2_B1 : statement_02 2 1 := by sorry
end TenChallenges
