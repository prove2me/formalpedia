-- Prove2me | Theorems.Thm_PPDifferentiation_ShortRun_asymmetric_equilibrium_profits
-- name    : PPDifferentiation.ShortRun.asymmetric_equilibrium_profits
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T12:59:06.764987+00:00
-- url     : https://prove2.me/theorems/6f1001c8-0540-4574-97a7-006a5489904b
-- title:
--   (4) — asymmetric subgame gross profits
-- statement:
--   Let $t>0$. With the targeting firm A at $-1/2$ and the uniform-price leader B at $1/2$, an optimal leader price exists, and every optimal leader price gives gross subgame profits
--
--   $$\pi_A^{AS}=\frac{t}{4},\qquad\pi_B^{AS}=\frac{t}{2}.$$
--
--   These are gross profits because the implementation cost was already sunk before positioning. They supply the asymmetric cells of Table 1 after the PP firm's cost is subtracted.
--
--   **Formalization Note** The leader chooses from all real prices; the result explicitly rules out vacuity by asserting existence of an optimum. The covered-market reservation value cancels.
-- source:
--   Li, Wang, Nault, Is Personalized Pricing Profitable When Firms Can Differentiate?, working paper, SSRN abstract 3881900 (version of August 3, 2021), §6, p. 25, display (4)

import Mathlib
import Definitions.Def_PPDifferentiation_ShortRun_Setting

namespace PPDifferentiation.ShortRun

theorem asymmetric_equilibrium_profits (t : ℝ) (ht : 0 < t) :
    (∃ p : ℝ, PPDifferentiation.Costless.IsLeaderOpt t (1/2) (-1/2) p) ∧
    ∀ p : ℝ, PPDifferentiation.Costless.IsLeaderOpt t (1/2) (-1/2) p →
      PPDifferentiation.Costless.followProf t (1/2) (-1/2) p = t/4 ∧
      PPDifferentiation.Costless.leadProf t (1/2) (-1/2) p = t/2 := by sorry

end PPDifferentiation.ShortRun
