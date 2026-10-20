-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_theorem6
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.theorem6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:36:48.521015+00:00
-- url     : https://prove2.me/theorems/21aaab05-4a14-45c6-a627-b35d446afe70
-- title:
--   Theorem 6 (Determinants of Markovian Channels)
-- statement:
--   All maps act complex-linearly on the same matrix algebra $M_d(\mathbb C)$, where $d\ge1$. Composition $AB$ applies $B$ first. Norms of maps are induced by the unnormalized Hilbert–Schmidt norm. Let $L$ have the canonical Lindblad representation with Hermitian Hamiltonian $H$, positive semidefinite coefficient matrix $G$, and a traceless Hilbert–Schmidt orthonormal basis $F_\alpha$. For $T=e^L$,
--
--   $$\det T=\exp(-d\operatorname{tr}G).$$
--
--   When $L$ is purely dissipative (that is, admits the canonical representation with zero Hamiltonian),
--
--   $$\|L\|\le-\frac2d\log\det T.$$
--
--   The determinant identity implies strict positivity, so the logarithm has positive argument. These formulas relate dissipative strength and determinant contraction.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 8, Theorem 6 (Determinants of Markovian Channels)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Theorem 6, PDF pp.8--9: the coefficient in the norm bound is 2/d.
The exponential determinant is strictly positive, so the logarithm is not evaluated at zero. -/
theorem theorem6 {d : ℕ} (hd : 0 < d)
    (F : Fin (d ^ 2 - 1) → Mat d)
    (htrace : ∀ a, (F a).trace = 0)
    (horth : ∀ a b, ((F a)ᴴ * F b).trace = if a = b then 1 else 0)
    (G : Matrix (Fin (d ^ 2 - 1)) (Fin (d ^ 2 - 1)) ℂ) (hG : G.PosSemidef)
    (H : Mat d) (hH : H.IsHermitian) :
    complexDet (NormedSpace.exp (canonicalGenerator F H G)) =
      (Real.exp (-(d : ℝ) * G.trace.re) : ℂ) ∧
    (PurelyDissipative (canonicalGenerator F H G) →
      hsOperatorNorm (canonicalGenerator F H G) ≤ -(2 / (d : ℝ)) *
        Real.log (determinant (NormedSpace.exp (canonicalGenerator F H G)))) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
