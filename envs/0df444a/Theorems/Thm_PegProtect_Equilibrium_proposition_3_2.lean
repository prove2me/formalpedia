-- Prove2me | Theorems.Thm_PegProtect_Equilibrium_proposition_3_2
-- name    : PegProtect.Equilibrium.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:37.572902+00:00
-- url     : https://prove2.me/theorems/b374a3fa-8bdd-41da-8a19-a59e3262a879
-- title:
--   Proposition 3.2, p. 17 — the market equilibrium is unique: ω* = max{0, (ϕ − d − β⁻¹(ϕ − 1))/(1 − d)}, N*_r = (ρ/ν)(1−ω*)/(1+ω*), N*_s = (2ρ/c)(1−ω*)/(1+ω*)
-- statement:
--   Consider the limit-order market with protected midpoint pegs, with flow cost of speed $c>0$, midpoint execution fee $0\le d<1$, investor gross surplus $\varphi>1$, discount rate $\delta>0$, and arrival rates $\rho,\nu>0$; the discount factor is $\beta=\exp(-\delta/\rho)\in(0,1)$. Then there is a unique market equilibrium $(\omega^*,N_r^*,N_s^*)$ in the sense of Definition 3.1. The equilibrium fraction of investors choosing midpoint pegs rather than market orders is
--   $$\omega^*=\max\Big\{0,\ \frac{\varphi-d-\beta^{-1}(\varphi-1)}{1-d}\Big\},$$
--   and the equilibrium masses of proprietary traders acting as market makers and as snipers are
--   $$N_r^*=\frac{\rho}{\nu}\Big(\frac{1-\omega^*}{1+\omega^*}\Big),\qquad N_s^*=\frac{2\rho}{c}\Big(\frac{1-\omega^*}{1+\omega^*}\Big).$$
--   Uniqueness means: this triple is a market equilibrium, and every market equilibrium $(\omega,N_r,N_s)$ equals it.
--
--   The result shows that, when pegs are protected from sniping, the peg share does not depend on the sniping intensity $\nu$, and gives closed forms for the populations of market makers and snipers.
--
--   **Formalization Note** The paper prints the restriction $\varphi\ge1$, but Assumption A4a (one of the hypotheses A1–A5 of the proposition) requires $\varphi>1$, and at $\varphi=1$ formula (3.6) gives $\omega^*=1$, which Definition 3.1 does not admit, while $\pi_p>\pi_m$ on $[0,1)$; so the statement uses $\varphi>1$. The fee restriction is the proposition's $d\ge0$. The condition $\beta\in(0,1)$ is not a separate hypothesis: it follows from $\delta,\rho>0$. The payoffs in Definition 3.1 are the defining sums under the steady state $q$, not their closed forms.
-- source:
--   Aldrich & Friedman, Order Protection through Delayed Messaging, SSRN 2999059 (version of March 3, 2019), p. 17, Proposition 3.2, (3.6)–(3.8); Definition 3.1 p. 17; Assumption A4a p. 11

import Mathlib
import Definitions.Def_PegProtect_Equilibrium_Model

namespace PegProtect.Equilibrium

theorem proposition_3_2 (P : Params) (hP : P.Standing) :
    IsMarketEquilibrium P (omegaStar P) (NrStar P) (NsStar P) ∧
    ∀ ω Nr Ns : ℝ, IsMarketEquilibrium P ω Nr Ns →
      ω = omegaStar P ∧ Nr = NrStar P ∧ Ns = NsStar P := by sorry

end PegProtect.Equilibrium
