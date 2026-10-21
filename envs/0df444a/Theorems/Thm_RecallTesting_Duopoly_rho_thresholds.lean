-- Prove2me | Theorems.Thm_RecallTesting_Duopoly_rho_thresholds
-- name    : RecallTesting.Duopoly.rho_thresholds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:42.485685+00:00
-- url     : https://prove2.me/theorems/b2157e8c-89b7-4f5c-95d8-f33ec3aaba40
-- title:
--   (A.5) and (A.3), p. 37 — recall-cost conditions for the two cutoff regions
-- statement:
--   Assume the standing assumptions $V,B,\rho>0$, $\delta\in(0,1]$, $\gamma,\theta\in(0,1)$, and let $N$, $\tilde\theta^{st}$, $D$, $\underline{\tilde\theta}^{nt}$, $\overline{\tilde\theta}^{nt}$ be as in (A.3)–(A.4). Then:
--
--   1. If the fixed recall cost exceeds $\tilde\rho^{st}$, then the dual-firm-test cutoff lies below $1$:
--   $$\rho>\tilde\rho^{st}\implies N>0\ \text{ and }\ \tilde\theta^{st}<1;$$
--   2. If the no-firm-test interval is a nondegenerate subinterval of $(0,1)$, then the fixed recall cost is below $\tilde\rho^{nt}$:
--   $$D>0\ \text{ and }\ 0<\underline{\tilde\theta}^{nt}<\overline{\tilde\theta}^{nt}<1\implies\rho<\tilde\rho^{nt}.$$
--
--   Here $\tilde\rho^{st}$ is (A.5) and $\tilde\rho^{nt}$ is the bound in (A.3). These are, respectively, a sufficient condition for an interior dual-test cutoff and a necessary condition for an interior no-test interval.
--
--   **Formalization Note** The first implication is the page's sufficient condition ("exists if"); the second is its necessary condition ("need to be satisfied"). The parameter $\theta$ itself plays no role. Since $\tilde\theta^{st}>0$ whenever $N>0$, the conclusion of item 1 expresses the page's "$0<\tilde\theta^{st}<1$".
-- source:
--   Kim, Koenigsberg & Ofek, I Don’t “Recall”, SSRN working paper 3492105 (Nov. 2019), p. 37 (PDF 38), proof of Proposition 2, (A.3) second condition and (A.5)

import Mathlib
import Definitions.Def_RecallTesting_Duopoly_Model

namespace RecallTesting.Duopoly

theorem rho_thresholds (P : Params) (hS : P.Standing) :
    (rhoST P < P.ρ → 0 < denST P ∧ thetaST P < 1) ∧
    ((0 < discNT P ∧ 0 < thetaNTlo P ∧ thetaNTlo P < thetaNThi P ∧ thetaNThi P < 1) →
      P.ρ < rhoNT P) := by sorry

end RecallTesting.Duopoly
