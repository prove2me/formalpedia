-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P25_windowTransform_coordinate_intertwining
-- name    : QAlgorithms.Papers.Independent.Renew46.P25.windowTransform_coordinate_intertwining
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:41:05.810992+00:00
-- url     : https://prove2.me/theorems/2b6c863a-fe0f-4f85-895b-21dd5ead2d4d
-- title:
--   Position and momentum intertwining
-- statement:
--   Let $n\ge1$, $\phi,f\in\mathcal S(\mathbb R^n)$, $\|\phi\|_2^2=1$, and $1\le j\le n$. For $z=(x,p)$ define the source's window transform by its actual kernel
--
--   $$U_\phi f(x,p)=(2\pi)^{-n/2}e^{ip\cdot x/2}\int e^{-ip\cdot y}\phi(x-y)f(y)\,dy.$$
--
--   Thus $U_\phi f(z)=(\pi/2)^{n/2}W(f,\overline\phi)(z/2)$ with the source's Wigner normalization. Then
--
--   $$U_\phi(x_jf)=\left(\frac{x_j}{2}+i\partial_{p_j}\right)U_\phi f,\qquad U_\phi(-i\partial_{x_j}f)=\left(\frac{p_j}{2}-i\partial_{x_j}\right)U_\phi f.$$
--
--   Both identities concern Schwartz inputs and their smooth transforms. They do not introduce everywhere-defined bounded position or momentum operators on L2.
-- source:
--   A Weyl Calculus on Symplectic Phase Space, arXiv:math-ph/0508024v2, PDF p. 32, Unnumbered (78): position and momentum intertwining

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P25

noncomputable section

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

open QAlgorithms.Papers.Independent.Next46.P37 (cayley inverseCayley diagonalHessian)

namespace QAlgorithms.Papers.Independent.Renew46.P25

/-- PDF p.32, (78): both coordinate intertwining identities, on the exact
Schwartz domain and with normalized complex window. The second printed xhat
is momentum, determined by (2),(77); no bounded L2 position/momentum is used. -/
theorem windowTransform_coordinate_intertwining (n : ℕ) (hn : 0 < n)
    (phi : SchwartzMap (ConfigurationEuclidean n) ℂ) (hphi : ‖phi.toLp 2 volume‖ ^ 2 = 1)
    (f : SchwartzMap (ConfigurationEuclidean n) ℂ) (j : Fin n) :
    windowTransform phi (configurationPosition j f) =
      groupedBoppPosition j (windowTransform phi f) ∧
    windowTransform phi (configurationMomentum j f) =
      groupedBoppMomentum j (windowTransform phi f) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P25

end
