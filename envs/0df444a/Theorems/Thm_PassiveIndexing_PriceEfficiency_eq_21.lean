-- Prove2me | Theorems.Thm_PassiveIndexing_PriceEfficiency_eq_21
-- name    : PassiveIndexing.PriceEfficiency.eq_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:49:31.79863+00:00
-- url     : https://prove2.me/theorems/c7a6a603-0fc4-4aaf-8795-331e24fbf5cc
-- title:
--   (21), p. 6226 — derivative with respect to the nonindexer count
-- statement:
--   Fix $0<N<m$ and a portfolio $x$. Differentiate the Schur-complement conditional-variance formula $V_x(N)$ of (20) with respect to the real continuation of the number of nonindexers. If $\theta(N)$ is defined by (19), then
--   $$
--   V_x'(N)=-\frac{1}{N^2}\theta(N)'\Sigma_{\varepsilon\varepsilon}\theta(N)\le 0,
--   \qquad
--   V_x'(N)<0\ \Longleftrightarrow\ \theta(N)\ne0.
--   $$
--   The derivative gives the direction of the efficiency change as investors move from nonindexing to indexing.
--
--   **Formalization Note** A derivative of the deterministic formula is asserted explicitly, so it cannot take a default value at a point where differentiability fails. Positive definiteness of both covariance matrices and $0<N<m$ keep the inverses and reciprocal meaningful.
-- source:
--   Baruch & Zhang, The Distortion in Prices Due to Passive Investing, Management Science 68(8), 2022, p. 6226, equation (21); https://doi.org/10.1287/mnsc.2021.4114

import Mathlib
import Definitions.Def_PassiveIndexing_PriceEfficiency_Model

namespace PassiveIndexing.PriceEfficiency

open Matrix

/-- Equation (21), p. 6226: differentiating the conditional-variance formula with
respect to the real continuation of the nonindexer count. -/
theorem eq_21 {n : ℕ} (m : ℕ)
    (Svv See : Matrix (Fin n) (Fin n) ℝ)
    (hSvv : Svv.PosDef) (hSee : See.PosDef)
    (N : ℝ) (hNpos : 0 < N) (hNlt : N < m)
    (x : Fin n → ℝ) :
    let d := -(1 / N ^ 2) *
      (thetaVec m Svv See x N ⬝ᵥ (See *ᵥ thetaVec m Svv See x N))
    HasDerivAt (condVarFormula m Svv See x) d N ∧
      d ≤ 0 ∧ (d < 0 ↔ thetaVec m Svv See x N ≠ 0) := by sorry

end PassiveIndexing.PriceEfficiency
