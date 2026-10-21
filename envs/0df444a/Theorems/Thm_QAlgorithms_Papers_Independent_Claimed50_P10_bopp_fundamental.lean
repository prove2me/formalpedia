-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P10_bopp_fundamental
-- name    : QAlgorithms.Papers.Independent.Claimed50.P10.bopp_fundamental
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:21:43.82332+00:00
-- url     : https://prove2.me/theorems/94b33322-3787-4c46-9063-bb246e5af658
-- title:
--   Bopp position and momentum from conjugation on the Schwartz domain
-- statement:
--   Let $n>0$ be an integer and let $f\in\mathcal S(\mathbb R^n_x\times\mathbb R^n_p)$. Work with $\hbar=1$ and Lebesgue measure. For a coordinate $j$, let $X_j f=x_jf$ and $D_{x,j}f=-i\partial_{x_j}f$. Put $\theta_0=(\sqrt7/7)\arccos(3/4)$ and let $S=\mathcal F_p^{-1}T(\theta_0)\mathcal F_p$, where $(\mathcal F_p f)(x,\eta)=(2\pi)^{-n/2}\int e^{-i\eta\cdot p}f(x,p)\,dp$ and $T(t)g(x,\eta)=g(x(-t),\eta(-t))$ uses the Hamiltonian flow of $H=2\xi_x\cdot\xi_p-x\cdot\xi_x-p\cdot\xi_p+4x\cdot p$. Define the Bopp operators by $X_{B,j}=SX_jS^{-1}$ and $D_{B,j}=SD_{x,j}S^{-1}$. For every $j$ and every $(x,p)$,
--
--   $$
--   (X_{B,j}f)(x,p)=x_jf(x,p)+\frac{i}{2}\partial_{p_j}f(x,p),\qquad
--   (D_{B,j}f)(x,p)=p_jf(x,p)-\frac{i}{2}\partial_{x_j}f(x,p).
--   $$
--
--   These coordinate identities specify the fundamental Bopp representation on its common Schwartz domain. They do not require normalization of $f$.
--
--   **Formalization Note** The local Fourier-integral helpers are evaluated only on Schwartz functions and expressions obtained from them by Fourier transforms, invertible linear pullbacks, coordinate multiplication, and differentiation. No formula for an arbitrary $L^2$ representative is used.
-- source:
--   Metaplectic formulation of the Wigner transform and applications, arXiv:1401.3388v1, PDF p. 16, Unnumbered: Bopp position and momentum operators

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P10

noncomputable section

open MeasureTheory

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Claimed50.P10

/-- PDF p.16, the two unnumbered fundamental-operator identities after (49).
Both equalities hold on the common Schwartz domain, for every coordinate.
S and its inverse are evaluated using (12); no L2 domain identity is asserted. -/
theorem bopp_fundamental {n : ℕ} (hn : 0 < n)
    (f : SchwartzMap (Configuration n × Configuration n) ℂ) :
    (∀ (j : Fin n) (z : Configuration n × Configuration n),
      boppPosition j (f : PhaseFunction n) z =
        (z.1 j : ℂ) * f z + Complex.I / 2 *
          (fderiv ℝ (f : PhaseFunction n) z) (0, Pi.single j 1)) ∧
    (∀ (j : Fin n) (z : Configuration n × Configuration n),
      boppMomentum j (f : PhaseFunction n) z =
        (z.2 j : ℂ) * f z - Complex.I / 2 *
          (fderiv ℝ (f : PhaseFunction n) z) (Pi.single j 1, 0)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P10

end
