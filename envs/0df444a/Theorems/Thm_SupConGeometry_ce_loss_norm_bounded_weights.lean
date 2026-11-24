-- Prove2me | Theorems.Thm_SupConGeometry_ce_loss_norm_bounded_weights
-- name    : SupConGeometry.ce_loss_norm_bounded_weights
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T01:14:12.412664+00:00
-- url     : https://prove2.me/theorems/60dad23d-4f08-43ee-afb2-ab4ca51bb12c
-- title:
--   Corollary 1: cross-entropy lower bound with norm-bounded weights
-- statement:
--   Under the hypotheses of Theorem 1 ($2\le K\le h+1$, $N\ge1$, $\rho>0$, $\|z_n\|\le\rho$, balanced $Y$), let $r>0$ and suppose $\|w_y\|\le r$ for every $y$. Then
--
--   $$\mathcal L_{CE}(Z,W;Y)\ \ge\ \log\Big(1+(K-1)\exp\Big(-\frac{K\rho r}{K-1}\Big)\Big),$$
--
--   with equality if and only if there are $\zeta_1,\dots,\zeta_K\in\mathbb R^h$ such that
--   1. (C1) $z_n=\zeta_{y_n}$ for all $n$;
--   2. (C2) $\{\zeta_y\}_y$ form a $\rho$-sphere-inscribed regular simplex;
--   3. (C3-r) $w_y=\frac{r}{\rho}\zeta_y$ for all $y$.
--
--   **Formalization Note** $r>0$ is implicit in the paper: its proof picks $\rho_W=r>0$. For $r=0$ the equality claim fails, since $W=0$ attains the bound for every $Z$.
-- source:
--   Graf, Hofer, Niethammer and Kwitt, Dissecting Supervised Contrastive Learning, ICML 2021, arXiv:2102.08817v4, Section 3.1, Corollary 1, p. 4; proof in Supplementary S2, p. 34; standing assumption K ≤ h+1 of Supplementary S2, p. 28

import Mathlib
import Definitions.Def_SupConGeometry_Basic

open Finset

namespace SupConGeometry

theorem ce_loss_norm_bounded_weights {N K h : ℕ} (hK : 2 ≤ K) (hKh : K ≤ h + 1) (hN : 0 < N)
    (ρ : ℝ) (hρ : 0 < ρ) (Z : Fin N → Rep h) (hZ : ∀ n, ‖Z n‖ ≤ ρ) (W : Fin K → Rep h)
    (Y : Fin N → Fin K) (hY : IsBalanced Y) (r : ℝ) (hr : 0 < r) (hW : ∀ y, ‖W y‖ ≤ r) :
    Real.log (1 + ((K : ℝ) - 1) * Real.exp (-((K : ℝ) * ρ * r / ((K : ℝ) - 1)))) ≤
      ceLoss Z W Y ∧
    (ceLoss Z W Y =
        Real.log (1 + ((K : ℝ) - 1) * Real.exp (-((K : ℝ) * ρ * r / ((K : ℝ) - 1)))) ↔
      ∃ ζ : Fin K → Rep h, (∀ n, Z n = ζ (Y n)) ∧ IsSphereInscribedRegularSimplex ζ ρ ∧
        ∀ y, W y = (r / ρ) • ζ y) := by sorry

end SupConGeometry
