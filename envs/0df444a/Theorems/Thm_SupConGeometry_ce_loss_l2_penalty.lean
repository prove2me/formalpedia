-- Prove2me | Theorems.Thm_SupConGeometry_ce_loss_l2_penalty
-- name    : SupConGeometry.ce_loss_l2_penalty
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T01:15:03.507104+00:00
-- url     : https://prove2.me/theorems/8cdf99c0-624a-4ac9-a554-4a01f5a80d41
-- title:
--   Corollary 2: cross-entropy lower bound with $L_2$ penalty
-- statement:
--   Under the hypotheses of Theorem 1 ($2\le K\le h+1$, $N\ge1$, $\rho>0$, $\|z_n\|\le\rho$, balanced $Y$), let $\lambda>0$ and let $r_{\mathcal W}=r_{\mathcal W}(\rho,\lambda)>0$ be the unique solution in $x$ of $2\lambda x-\rho/(\exp(\frac{K\rho x}{K-1})+K-1)=0$. Then
--
--   $$\mathcal L_{CE}(Z,W;Y)+\lambda\|W\|_F^2\ \ge\ \log\Big(1+(K-1)\exp\Big(-\rho\frac{K}{K-1}r_{\mathcal W}\Big)\Big)+\lambda K r_{\mathcal W}^2,$$
--
--   with equality if and only if there are $\zeta_1,\dots,\zeta_K\in\mathbb R^h$ such that
--   1. (C1) $z_n=\zeta_{y_n}$ for all $n$;
--   2. (C2) $\{\zeta_y\}_y$ form a $\rho$-sphere-inscribed regular simplex;
--   3. (C3-wd) $w_y=\frac{r_{\mathcal W}}{\rho}\zeta_y$ for all $y$.
--
--   So weight decay removes the need for an explicit norm constraint on the classifier: at the optimum the weights form a regular simplex of radius $r_{\mathcal W}(\rho,\lambda)$.
-- source:
--   Graf, Hofer, Niethammer and Kwitt, Dissecting Supervised Contrastive Learning, ICML 2021, arXiv:2102.08817v4, Section 3.1, Corollary 2, p. 5; proof in Supplementary S2, p. 35; standing assumption K ≤ h+1 of Supplementary S2, p. 28

import Mathlib
import Definitions.Def_SupConGeometry_Basic

open Finset

namespace SupConGeometry

theorem ce_loss_l2_penalty {N K h : ℕ} (hK : 2 ≤ K) (hKh : K ≤ h + 1) (hN : 0 < N)
    (ρ : ℝ) (hρ : 0 < ρ) (Z : Fin N → Rep h) (hZ : ∀ n, ‖Z n‖ ≤ ρ) (W : Fin K → Rep h)
    (Y : Fin N → Fin K) (hY : IsBalanced Y) (lam : ℝ) (hlam : 0 < lam) :
    Real.log (1 + ((K : ℝ) - 1) *
          Real.exp (-(ρ * ((K : ℝ) / ((K : ℝ) - 1)) * ceL2Radius K ρ lam))) +
        lam * (K : ℝ) * ceL2Radius K ρ lam ^ 2 ≤ ceLoss Z W Y + lam * frobNorm W ^ 2 ∧
    (ceLoss Z W Y + lam * frobNorm W ^ 2 =
        Real.log (1 + ((K : ℝ) - 1) *
            Real.exp (-(ρ * ((K : ℝ) / ((K : ℝ) - 1)) * ceL2Radius K ρ lam))) +
          lam * (K : ℝ) * ceL2Radius K ρ lam ^ 2 ↔
      ∃ ζ : Fin K → Rep h, (∀ n, Z n = ζ (Y n)) ∧ IsSphereInscribedRegularSimplex ζ ρ ∧
        ∀ y, W y = (ceL2Radius K ρ lam / ρ) • ζ y) := by sorry

end SupConGeometry
