-- Prove2me | Theorems.Thm_TalagrandConc_TwoPoint_cor_2_3_2_mgf
-- name    : TalagrandConc.TwoPoint.cor_2_3_2_mgf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:44.199982+00:00
-- url     : https://prove2.me/theorems/3deaa159-9544-42c1-9982-0c58191f02f9
-- title:
--   Corollary 2.3.2, Eq. (2.3.4) — $\int e^{tf}\,dP \le P(A)^{-\alpha}\exp N[p(1-p)(1+1/\alpha)t^2/2+Kt^3]$
-- statement:
--   Let $\Omega=\{0,1\}$, let $\mu$ be the probability with $\mu(\{1\})=p$, let $P=\mu^N$ on $\Omega^N$, and let $f(A,x)$ be the Hamming distance from $x\in\Omega^N$ to $A\subseteq\Omega^N$.
--
--   There is a universal constant $K>0$ such that for every $p\in[0,1]$, every $N\ge 0$, every $A\subseteq\Omega^N$, every $\alpha\ge 1$ and every $0\le t\le 1$,
--   $$\int e^{t f(A,x)}\,dP(x)\le\frac{1}{P(A)^{\alpha}}\exp N\Big[p(1-p)\Big(1+\frac1\alpha\Big)\frac{t^2}{2}+Kt^3\Big].$$
--
--   This is a Gaussian-type exponential moment bound whose leading coefficient carries the variance $p(1-p)$ of one coordinate, so it is sharper than the bias-free bound when $p$ is close to $0$ or $1$.
--
--   **Formalization Note** $K$ is quantified before $p$, $N$, $A$, $\alpha$ and $t$, so it is a single absolute constant. The right-hand side is computed in $[0,\infty]$, so $P(A)=0$ gives $+\infty$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 89, Corollary 2.3.2, Eq. (2.3.4)

import Mathlib
import Definitions.Def_TalagrandConc_TwoPoint_Basic

open MeasureTheory
open scoped ENNReal NNReal

namespace TalagrandConc.TwoPoint

/-- Talagrand (1995), Corollary 2.3.2, Eq. (2.3.4), p. 89. There is a universal constant
`K` such that for all `p ∈ [0,1]`, `N`, `A ⊆ {0,1}^N`, `α ≥ 1`, `0 ≤ t ≤ 1`,
`∫ e^{t f(A,x)} dP(x) ≤ P(A)^{-α} exp N[p(1-p)(1 + 1/α) t²/2 + K t³]`. -/
theorem cor_2_3_2_mgf :
    ∃ K : ℝ, 0 < K ∧ ∀ (p : unitInterval) (N : ℕ) (A : Set (Fin N → Bool))
      (α : ℝ), 1 ≤ α → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (∫⁻ x, TalagrandConc.OnePoint.expMul t (hammingDistToSet A x) ∂(productMeasure N p))
        ≤ ENNReal.ofReal (Real.exp (N * ((p : ℝ) * (1 - p) * (1 + 1 / α) * t ^ 2 / 2
              + K * t ^ 3)))
          / (productMeasure N p A) ^ α := by sorry

end TalagrandConc.TwoPoint
