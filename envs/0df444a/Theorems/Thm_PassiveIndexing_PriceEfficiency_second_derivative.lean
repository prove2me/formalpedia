-- Prove2me | Theorems.Thm_PassiveIndexing_PriceEfficiency_second_derivative
-- name    : PassiveIndexing.PriceEfficiency.second_derivative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:49:20.235807+00:00
-- url     : https://prove2.me/theorems/fe9fb465-0b53-4f9f-93f2-39b6aafb28ff
-- title:
--   §6.1, p. 6227 — nonnegative second derivative (printed inverse sign corrected)
-- statement:
--   Fix $0<N<m$ and a stock portfolio $x$. The derivative from (21) has a derivative at $N$, and this second derivative of the conditional-variance formula is nonnegative:
--   $$
--   \frac{d^2 V_x}{dN^2}(N)
--   =\frac{2}{N^3}\theta'\Sigma_{\varepsilon\varepsilon}\theta
--   -\frac{2}{N^4}(D w)'\Sigma_{yy}(N)^{-1}(D w)\ge0,
--   $$
--   where $w=(\theta,q)$ and $D=\operatorname{diag}(\Sigma_{\varepsilon\varepsilon},0)$. This is the convexity assertion used for the increasing rate in Theorem 3.
--
--   **Formalization Note** The displayed argument on p. 6227 omits the minus sign in $d(\Sigma_{yy}^{-1})/dN=-\Sigma_{yy}^{-1}(d\Sigma_{yy}/dN)\Sigma_{yy}^{-1}$. The stated derivative value corrects that step while retaining the paper's nonnegativity conclusion. The explicit derivative assertion avoids a default zero at a nondifferentiable point. The real interval $0<N<m$ extends the integer counts for calculus.
-- source:
--   Baruch & Zhang, The Distortion in Prices Due to Passive Investing, Management Science 68(8), 2022, p. 6227, §6.1 second-derivative display (printed inverse-derivative sign corrected); https://doi.org/10.1287/mnsc.2021.4114

import Mathlib
import Definitions.Def_PassiveIndexing_PriceEfficiency_Model

namespace PassiveIndexing.PriceEfficiency

open Matrix

/-- §6.1 second-derivative display, p. 6227. The printed argument omits a minus sign
in the inverse-matrix derivative; this statement gives the corrected derivative value
and retains the asserted nonnegativity. -/
theorem second_derivative {n : ℕ} (m : ℕ)
    (Svv See : Matrix (Fin n) (Fin n) ℝ)
    (hSvv : Svv.PosDef) (hSee : See.PosDef)
    (N : ℝ) (hNpos : 0 < N) (hNlt : N < m)
    (x : Fin n → ℝ) :
    let d2 :=
      2 / N ^ 3 * (thetaVec m Svv See x N ⬝ᵥ (See *ᵥ thetaVec m Svv See x N)) -
      2 / N ^ 4 *
        ((Dblk See *ᵥ rowCoef m Svv See x N) ⬝ᵥ
          ((Syy m Svv See N)⁻¹ *ᵥ (Dblk See *ᵥ rowCoef m Svv See x N)))
    HasDerivAt
      (fun N' => -(1 / N' ^ 2) *
        (thetaVec m Svv See x N' ⬝ᵥ (See *ᵥ thetaVec m Svv See x N')))
      d2 N ∧ 0 ≤ d2 := by sorry

end PassiveIndexing.PriceEfficiency
