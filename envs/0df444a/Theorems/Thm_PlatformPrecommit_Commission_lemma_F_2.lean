-- Prove2me | Theorems.Thm_PlatformPrecommit_Commission_lemma_F_2
-- name    : PlatformPrecommit.Commission.lemma_F_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:12.735985+00:00
-- url     : https://prove2.me/theorems/f56c8416-6f0c-4125-b2c0-393298c30d67
-- title:
--   Lemma F.2, Online Appendix p. 30 — commission-game prices equate demand and supply
-- statement:
--   Fix $\Omega>0$, $0\leq\beta,\gamma<1$, and a pair of pay-out ratios $\alpha_i\in(0,1)$. At any second-stage Nash equilibrium in which both platforms earn positive profits, each platform's demand equals its supply:
--
--   $$d_i(p)=s_i(\alpha p),\qquad i=1,2.$$
--
--   This equality is the market-clearing relation used to determine second-stage prices in the commission game.
--
--   **Formalization Note** Positive profits exclude the zero-profit price equilibria admitted by the positive-part demand and supply formulas. Prices themselves range over all real numbers.
-- source:
--   Hu, Liu, Precommitments in Two-Sided Market Competition, submitted manuscript (SSRN 3734828; TSpace), Online Appendix p. 30, Lemma F.2

import Mathlib
import Definitions.Def_PlatformPrecommit_Commission_Setting

namespace PlatformPrecommit.Commission

/-- Lemma F.2, on the positive-profit equilibria used in the appendix derivation. -/
theorem lemma_F_2 (M : Model) (hM : M.Standing)
    (α p : Fin 2 → ℝ) (hα : AdmissibleAlpha α)
    (hp : IsCSubNE M α p) (hpos : ∀ i, 0 < profC M α p i) :
    ∀ i, demand M p i = supply M (wageC α p) i := by sorry

end PlatformPrecommit.Commission
