-- Prove2me | Theorems.Thm_PassiveIndexing_PriceEfficiency_lemma_2
-- name    : PassiveIndexing.PriceEfficiency.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:49:13.236644+00:00
-- url     : https://prove2.me/theorems/512d6016-1e2b-4ab9-a8cc-c2e269c7cc7e
-- title:
--   Lemma 2, p. 6226 — market portfolios are exactly those with θ = 0
-- statement:
--   Fix a real $N$ with $0<N<m$, a stock portfolio $x$, and the coefficients $(\theta',q)=x'\Sigma_{vy}\Sigma_{yy}(N)^{-1}$ from (19). The following three conditions are equivalent:
--
--   1. $x$ is a scalar multiple of the market portfolio $\mathbf 1$.
--   2. $x=q\mathbf 1$.
--   3. $\theta=0$.
--
--   The characterization identifies exactly when the first-order change in price efficiency can vanish.
--
--   **Formalization Note** The real variable $N\in(0,m)$ extends the paper's integer $|NI|$ to the interval used in its derivative argument. Both covariance matrices are assumed positive definite; no sign restriction is placed on the scalar multiple of $\mathbf 1$.
-- source:
--   Baruch & Zhang, The Distortion in Prices Due to Passive Investing, Management Science 68(8), 2022, p. 6226, Lemma 2 and equation (19); proof p. 6232; https://doi.org/10.1287/mnsc.2021.4114

import Mathlib
import Definitions.Def_PassiveIndexing_PriceEfficiency_Model

namespace PassiveIndexing.PriceEfficiency

open Matrix

/-- Lemma 2, p. 6226: the three characterizations of market-portfolio multiples.
The real variable `N ∈ (0,m)` extends the paper's integer `|NI|` for differentiation. -/
theorem lemma_2 {n : ℕ} (m : ℕ)
    (Svv See : Matrix (Fin n) (Fin n) ℝ)
    (hSvv : Svv.PosDef) (hSee : See.PosDef)
    (N : ℝ) (hNpos : 0 < N) (hNlt : N < m)
    (x : Fin n → ℝ) :
    ((∃ c : ℝ, x = c • marketPortfolio n) ↔
      x = qCoef m Svv See x N • marketPortfolio n) ∧
    (x = qCoef m Svv See x N • marketPortfolio n ↔
      thetaVec m Svv See x N = 0) := by sorry

end PassiveIndexing.PriceEfficiency
