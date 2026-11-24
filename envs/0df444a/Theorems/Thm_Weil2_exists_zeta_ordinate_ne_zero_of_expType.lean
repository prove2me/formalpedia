-- Prove2me | Theorems.Thm_Weil2_exists_zeta_ordinate_ne_zero_of_expType
-- name    : Weil2.exists_zeta_ordinate_ne_zero_of_expType
-- status  : Proved
-- author  : @xuanji
-- created : 2026-11-24T04:16:57.151319+00:00
-- url     : https://prove2.me/theorems/851838e1-12a2-47ff-805e-08b0c011c7f0
-- title:
--   Under RH, an entire function of exponential type cannot vanish at all zeta ordinates
-- statement:
--   Assume the Riemann hypothesis. Let $F$ be an entire function of exponential type, $|F(z)|\le Ce^{A|z|}$, which does not vanish at some real point $t_0$. Then there is a zero $\rho=\tfrac12+i\gamma$ of $\zeta$ with $\gamma>0$, of positive finite order, such that $F(\gamma)\ne0$. The reason: by Jensen's inequality $F$ has $O(T)$ zeros in $[0,T]$, while under RH the zeros of $\zeta$ have multiplicity $o(\log\gamma)$ and $N(T)\gg T\log T$, so the number of distinct ordinates up to $T$ is superlinear. Applied to the Fourier transform of a compactly supported test function, this is the nondegeneracy behind strict Weil positivity.
-- source:
--   Broughan, Equivalents of the Riemann Hypothesis, Vol. II, Thm 9.6 (strict positivity); Jensen's formula; Titchmarsh §14.13.

import Mathlib

namespace Weil2

theorem exists_zeta_ordinate_ne_zero_of_expType (hRH : RiemannHypothesis) (F : ℂ → ℂ)
    (hF : Differentiable ℂ F) (C A : ℝ) (hb : ∀ z, ‖F z‖ ≤ C * Real.exp (A * ‖z‖)) (t0 : ℝ)
    (h0 : F t0 ≠ 0) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.im ∧ 0 < analyticOrderNatAt riemannZeta ρ ∧
      F (ρ.im : ℂ) ≠ 0 := by sorry

end Weil2
