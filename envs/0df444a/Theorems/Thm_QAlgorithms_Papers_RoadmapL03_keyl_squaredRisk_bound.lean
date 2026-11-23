-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapL03_keyl_squaredRisk_bound
-- name    : QAlgorithms.Papers.RoadmapL03.keyl_squaredRisk_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-23T11:40:25.740936+00:00
-- url     : https://prove2.me/theorems/332931c4-d826-4bb3-a289-5687f0523d9b
-- title:
--   Keyl estimator: squared Frobenius risk at most (4d-3)/n
-- statement:
--   Let $d,n\ge1$ and let $\rho$ be a $d\times d$ density matrix (possibly singular) with sorted spectrum $\alpha$. Draw $\lambda\sim\mathrm{SW}^n(\alpha)$ by weak Schur sampling and then $U\sim\mathrm K_\lambda(\rho)$ by Keyl's measurement. Equivalently, draw $(\lambda,U)$ from the joint law with density $\dim(\mathrm{Sp}_\lambda)\dim(V^d_\lambda)\Delta_\lambda(U^\dagger\rho U)$ relative to counting measure times probability Haar measure. Report
--
--   $$\widehat\rho=U\operatorname{diag}(\lambda_1/n,\dots,\lambda_d/n)\,U^\dagger .$$
--
--   Then the expected squared Frobenius error satisfies
--
--   $$\mathbf E\,\|\widehat\rho-\rho\|_F^2\le\frac{4d-3}{n}.$$
--
--   This is the risk guarantee of O'Donnell–Wright's Theorem 1.2. It shows that Keyl's estimator learns an unknown $d$-dimensional state to Frobenius error $\varepsilon$ from $O(d/\varepsilon^2)$ copies.
--
--   **Formalization Note.** The risk is `Tomography.keylSquaredRisk`, the lower Lebesgue integral of the squared Frobenius loss against `Tomography.keylJointLaw`, valued in $[0,\infty]$.
-- source:
--   R. O'Donnell and J. Wright, Efficient quantum tomography, arXiv:1508.01907v2, Theorem 1.2 (p. 2), proof in Section 4.2 (eqs. (17)-(20)) using Lemma 3.1 and Corollary 4.7. https://arxiv.org/abs/1508.01907v2

import Definitions.Def_QAlgorithms_Defs_KeylTomography
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_QAlgorithms_Defs_TomographyOutcomes
set_option autoImplicit false

noncomputable section

namespace QAlgorithms.Papers.RoadmapL03

theorem keyl_squaredRisk_bound (d n : ℕ) (hd : 0 < d) (hn : 0 < n)
    (rho : Matrix (Fin d) (Fin d) ℂ) (density : IsDensityMatrix rho) :
    Tomography.keylSquaredRisk hd hn rho density ≤ ENNReal.ofReal (((4 : ℝ) * d - 3) / n) := by sorry

end QAlgorithms.Papers.RoadmapL03
