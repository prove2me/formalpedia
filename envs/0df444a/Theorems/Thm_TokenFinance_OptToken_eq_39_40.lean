-- Prove2me | Theorems.Thm_TokenFinance_OptToken_eq_39_40
-- name    : TokenFinance.OptToken.eq_39_40
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:19:10.467982+00:00
-- url     : https://prove2.me/theorems/cf36aea1-a290-4e4f-a933-caa60fb120c6
-- title:
--   Equations (39)–(40): the transformed break-even cubic is strictly increasing
-- statement:
--   Suppose $0<c<\theta$ and the project's NPV $V=E_\theta[\pi^m]-C_0$ is positive. Let
--
--   $$f(t)=\frac{t^3}{3}-\frac{\theta-c}{2}t^2+\left(\frac{(\theta-c)^2}{4}+\frac{\theta V}{2c}\right)t-\frac\theta2 C_0.$$
--
--   The function $f$ is strictly increasing on the real line. For every $t>-c$, the token break-even equation (16) holds exactly when $f(t)=0$.
--
--   Strict monotonicity gives uniqueness of the economically admissible root. **Formalization Note** The lower bound $t>-c$ is needed to clear the denominator $c+t$ in (16); the contract ultimately uses $t>0$.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 41 (PDF p. 42), (39)–(40)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Definitions.Def_TokenFinance_OptToken_RootPolynomial

namespace TokenFinance.OptToken

theorem eq_39_40 (c C0 θ : ℝ) (hc : 0 < c) (hcθ : c < θ)
    (hnpv : 0 < TokenFinance.Debt.npv c C0 θ) :
    StrictMono (rootPolynomial c C0 θ) ∧
      ∀ t : ℝ, -c < t →
        (TokenFinance.Debt.tokenBreakEven c C0 θ t ↔ rootPolynomial c C0 θ t = 0) := by sorry

end TokenFinance.OptToken
