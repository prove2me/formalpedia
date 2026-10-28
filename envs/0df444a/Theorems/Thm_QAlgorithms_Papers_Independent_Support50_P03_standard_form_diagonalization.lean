-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P03_standard_form_diagonalization
-- name    : QAlgorithms.Papers.Independent.Support50.P03.standard_form_diagonalization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:23:46.179922+00:00
-- url     : https://prove2.me/theorems/3d1965b5-02d9-4bed-90bf-984a97f59a62
-- title:
--   Signed standard-form symplectic decomposition and reduced Gibbs matrix
-- statement:
--   Let $a,b,c\in\mathbb R$ and suppose that
--   $V=\left[\begin{smallmatrix}a&c\\c&b\end{smallmatrix}\right]\oplus\left[\begin{smallmatrix}a&-c\\-c&b\end{smallmatrix}\right]$ is a physical covariance matrix with vacuum covariance $I/2$. Set $V_0=\left[\begin{smallmatrix}a&c\\c&b\end{smallmatrix}\right]$, $C=I_2\oplus\sigma_Z$, $y=(a+b)^2-4c^2$ and
--
--   $$
--   \nu_\pm=\frac{\sqrt y\pm(b-a)}2,\quad D=\operatorname{diag}(\nu_-,\nu_+),\quad
--   \omega_+=\sqrt{\frac{a+b+\sqrt y}{2\sqrt y}},\quad
--   \omega_-=\operatorname{sgn}(c)\sqrt{\frac{a+b-\sqrt y}{2\sqrt y}},\quad
--   S_0=\begin{bmatrix}\omega_+&\omega_-\\\omega_-&\omega_+\end{bmatrix},
--   $$
--
--   where $\operatorname{sgn}(0)=0$. Then $a,b\ge1/2$, $y>0$, $\nu_\pm\ge1/2$, and
--
--   $$
--   |c|\le\min\!\left\{\sqrt{(a-1/2)(b+1/2)},\sqrt{(a+1/2)(b-1/2)}\right\},\quad
--   V_0=S_0DS_0^T,\quad S=C(S_0\oplus S_0)C,\quad
--   S\Omega S^T=\Omega,\quad V=S(D\oplus D)S^T.
--   $$
--
--   If $\nu_\pm>1/2$, put $A=\operatorname{arcoth}(2D)$ and define $G=-2\Omega S(A\oplus A)S^T\Omega$ as in (6). Its reduced expression is
--
--   $$
--   G=-2\Omega C\big((S_0AS_0)\oplus(S_0AS_0)\big)C\Omega.
--   $$
--
--   This gives explicit normal modes and a two-dimensional Gibbs factor. The signed off-diagonal square root extends the printed parametrization to physical standard covariances with either sign of $c$.
-- source:
--   Gaussian hypothesis testing and quantum illumination, arXiv:1608.06991v2, PDF p. 12, Appendix E, (E4)–(E9), corrected signs

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P03

noncomputable section

open Filter

open scoped BigOperators ComplexOrder Topology Matrix

namespace QAlgorithms.Papers.Independent.Support50.P03

open QAlgorithms.Papers.Independent.Dependency50.P10
  (Phase complexify sigma thermalCovariance)

open QAlgorithms.Papers.Independent.Frontier30.P02 (PhaseMatrix)

/-- Appendix E, arXiv:1608.06991v2, PDF p.12, (E4)--(E9).
Source correction: printed (E3) has c rather than abs c and (E5) has a positive
omega_minus. Physicality is retained and omega_minus is signed by c (zero at
c=0), so reconstruction also holds for negative c. Denominators and spectral
bounds are conclusions, not assumed diagonalization identities. Gibbs equality
is asserted only when the covariance is faithful; pure-mode diagonalization
is included. The correction awaits independent moderation. -/
theorem standard_form_diagonalization (a b c : ℝ)
    (hV : HalfVacuumCovariance (standardCovariance a b c)) :
    (1 / 2 : ℝ) ≤ a ∧ (1 / 2 : ℝ) ≤ b ∧
    |c| ≤ min (Real.sqrt ((a - 1 / 2) * (b + 1 / 2)))
      (Real.sqrt ((a + 1 / 2) * (b - 1 / 2))) ∧
    0 < standardY a b c ∧
    (∀ j, (1 / 2 : ℝ) ≤ standardSpectrum a b c j) ∧
    standardV0 a b c = standardS0 a b c * Matrix.diagonal (standardSpectrum a b c) *
      (standardS0 a b c).transpose ∧
    standardS a b c ∈ Matrix.symplecticGroup (Fin 2) ℝ ∧
    standardCovariance a b c = standardS a b c *
      thermalCovariance (standardSpectrum a b c) * (standardS a b c).transpose ∧
    (FaithfulSpectrum (standardSpectrum a b c) →
      gibbsMatrix (standardS a b c) (standardSpectrum a b c) =
        (-2 : ℝ) • (sigma 2 * standardParity * repeatBlock (standardReducedGibbs a b c) *
          standardParity * sigma 2)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P03

end
