-- Prove2me | Theorems.Thm_TokenFinance_OptToken_proposition_3
-- name    : TokenFinance.OptToken.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:50.148775+00:00
-- url     : https://prove2.me/theorems/5059da9e-2b1e-4889-88d0-0faddad04e63
-- title:
--   Proposition 3: an optimal token pre-sale with a unique break-even size
-- statement:
--   Let marginal cost satisfy $0<c<\theta$, let the set-up cost satisfy $C_0>0$, and suppose the project has positive NPV $V=E_\theta[\pi^m]-C_0$. Under the pre-sale contract with share $\alpha_t=t/(t+c)$, the investor refund and redemption rule, and realized entrepreneur and investor payments $\pi_t^e(x,q)$ and $I_t(x,q)$:
--
--   1. For every $t>0$, demand realization $x$, and feasible output $q\ge0$, the monopoly output $q^m(x)$ maximizes the entrepreneur's realized payment: $\pi_t^e(x,q)\le\pi_t^e(x,q^m(x))$.
--   2. For every $t\in(0,(\theta-c)/2)$, investors break even at $E_\theta[I_t(x,q^m(x))]=C_0+ct$ exactly when $t$ solves equation (16).
--   3. There is exactly one positive solution of (16), and it lies in $(0,(\theta-c)/2)$.
--   4. For every positive solution of (16), $E_\theta[\pi_t^e(x,q^m(x))]=V$.
--
--   $$\frac{c}{c+t}\frac{2}{3\theta}\left(\frac{\theta-c}{2}-t\right)^3=\frac{(\theta-c)^3}{12\theta}-C_0.$$
--
--   Together these clauses formalize the contract of Proposition 3 and its break-even and expected-profit claims. **Formalization Note** The payments and expectations are computed from realized payoffs. Optimality is over output choices under this contract, as in the paper's discussion; the paper does not define a broader mathematical space of contracts. The monopoly output need not be a unique maximizer when it is at most $t$.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 24 (PDF p. 25), Proposition 3 and (16); Appendix A, pp. 39–41 (PDF pp. 40–42), proof of Proposition 3

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.OptToken

theorem proposition_3 (c C0 θ : ℝ) (hc : 0 < c) (hcθ : c < θ)
    (hC0 : 0 < C0) (hnpv : 0 < TokenFinance.Debt.npv c C0 θ) :
    (∀ t : ℝ, 0 < t → ∀ x q : ℝ, 0 ≤ q →
      TokenFinance.Debt.tokEnt c t x q ≤ TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) ∧
    (∀ t : ℝ, 0 < t → t < (θ - c) / 2 →
      (TokenFinance.Debt.expect θ (fun x => TokenFinance.Debt.tokInv c t x (TokenFinance.Debt.qm c x)) = C0 + c * t ↔
        TokenFinance.Debt.tokenBreakEven c C0 θ t)) ∧
    (∃ t : ℝ, 0 < t ∧ t < (θ - c) / 2 ∧ TokenFinance.Debt.tokenBreakEven c C0 θ t ∧
      ∀ u : ℝ, 0 < u → TokenFinance.Debt.tokenBreakEven c C0 θ u → u = t) ∧
    (∀ t : ℝ, 0 < t → TokenFinance.Debt.tokenBreakEven c C0 θ t →
      TokenFinance.Debt.expect θ (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) = TokenFinance.Debt.npv c C0 θ) := by sorry

end TokenFinance.OptToken
