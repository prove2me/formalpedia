-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P21_epsilon_region_exact
-- name    : QAlgorithms.Papers.Independent.Next46.P21.epsilon_region_exact
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:38:38.317931+00:00
-- url     : https://prove2.me/theorems/ebd504e9-815a-43b3-aba6-4b4917658c2c
-- title:
--   Exact spectral error and the epsilon region
-- statement:
--   Let $\varepsilon>0$, $\theta\in\mathbb R$, $k\in\mathbb N$, and $u,t\in\mathbb Z[\omega]$, where $\omega=e^{i\pi/4}$. Assume $\overline u u+\overline t t=2^k$. Put $\hat u=u/\sqrt{2^k}$, $\hat t=t/\sqrt{2^k}$, $z=e^{-i\theta/2}$, and
--
--   $$
--   U=\begin{pmatrix}\hat u&-\overline{\hat t}\\\hat t&\overline{\hat u}\end{pmatrix}.
--   $$
--
--   Then $U\in SU(2)$ and its absolute spectral error satisfies
--
--   $$
--   \|U-R_z(\theta)\|_{\mathrm{op}}^2=|\hat u-z|^2+|\hat t|^2=2-2\operatorname{Re}(\overline{\hat u}z).
--   $$
--
--   Writing $D=\{w\in\mathbb C:|w|^2\le1\}$ and $\mathcal R_\varepsilon=\{w\in D:\operatorname{Re}(\overline w z)\ge1-\varepsilon^2/2\}$, one has
--
--   $$
--   \|U-R_z(\theta)\|_{\mathrm{op}}\le\varepsilon\quad\Longleftrightarrow\quad\hat u\in\mathcal R_\varepsilon.
--   $$
--
--   Here $R_z(\theta)=\operatorname{diag}(e^{-i\theta/2},e^{i\theta/2})$. The equivalence applies to the normalized entry and retains global phase.
-- source:
--   Efficient Clifford+T approximation of single-qubit operators, arXiv:1212.6253v2, PDF p. 8, §6.1: exact operator-error characterization

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P21

open Set

open scoped ComplexConjugate

/-- Section 6.1, equations (23)-(27), PDF pp.8-9: exact absolute spectral-error characterization.
The geometric coordinate is normalized; no global phase is discarded. -/
theorem epsilon_region_exact (eps theta : ℝ) (k : ℕ) (u t : ℂ)
    (heps : 0 < eps) (hu : IsCyclotomicInteger u) (ht : IsCyclotomicInteger t)
    (hnorm : star u * u + star t * t = (2 : ℂ) ^ k) :
    completion k u t ∈ Matrix.specialUnitaryGroup Bool ℂ ∧
    QAlgorithms.specNorm (completion k u t - zRotation theta) ^ 2 =
      Complex.normSq (u / (Real.sqrt ((2 : ℝ) ^ k) : ℂ) - zPhase theta) +
        Complex.normSq (t / (Real.sqrt ((2 : ℝ) ^ k) : ℂ)) ∧
    QAlgorithms.specNorm (completion k u t - zRotation theta) ^ 2 =
      2 - 2 * (star (u / (Real.sqrt ((2 : ℝ) ^ k) : ℂ)) * zPhase theta).re ∧
    (QAlgorithms.specNorm (completion k u t - zRotation theta) ≤ eps ↔
      (u / (Real.sqrt ((2 : ℝ) ^ k) : ℂ)) ∈ epsilonRegion eps theta) := by sorry

end QAlgorithms.Papers.Independent.Next46.P21

end
