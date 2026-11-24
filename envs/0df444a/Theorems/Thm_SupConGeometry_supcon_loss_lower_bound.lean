-- Prove2me | Theorems.Thm_SupConGeometry_supcon_loss_lower_bound
-- name    : SupConGeometry.supcon_loss_lower_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T01:13:03.25783+00:00
-- url     : https://prove2.me/theorems/e49a8c1a-81ed-4ce1-b277-3e55df56c922
-- title:
--   Theorem 2: supervised contrastive loss is minimized exactly by collapse onto a regular simplex
-- statement:
--   Let $h,N,K\in\mathbb N$ with $2\le K\le h+1$, let $b\ge3$ be the batch size, and let $\rho>0$. Let $Z=(z_1,\dots,z_N)$ be a configuration on the sphere $\mathbb S^{h-1}_\rho$ with balanced labels $Y\in[K]^N$. Then
--
--   $$\mathcal L_{SC}(Z;Y)\ \ge\ \sum_{l=2}^b l\,M_l\log\Big(l-1+(b-l)\exp\Big(-\frac{K\rho^2}{K-1}\Big)\Big),\qquad M_l=\sum_y\big|\{B\in\mathcal B:|B_y|=l\}\big|.$$
--
--   Equality holds if and only if there are $\zeta_1,\dots,\zeta_K\in\mathbb R^h$ such that
--   1. (C1) $z_n=\zeta_{y_n}$ for all $n\in[N]$, and
--   2. (C2) $\{\zeta_y\}_y$ form a $\rho$-sphere-inscribed regular simplex.
--
--   So the supervised contrastive loss over all batches is minimal exactly when every class collapses to a single point and these points are the vertices of a regular simplex on the sphere.
--
--   **Formalization Note** $K\ge2$ is implicit in the factor $\frac{K}{K-1}$. For $K=1$ the collapsed configuration attains the bound but no simplex exists. $b\ge3$ and $K\le h+1$ are the paper's standing assumptions (Section 2 and Supplementary S1). The loss sums over all multisets of $b$ indices, as in Definition 2.
-- source:
--   Graf, Hofer, Niethammer and Kwitt, Dissecting Supervised Contrastive Learning, ICML 2021, arXiv:2102.08817v4, Section 3.2, Theorem 2, p. 5 (restated Supplementary S1, p. 12; final step Lemma 11, eq. (114), p. 26); standing assumptions Section 2, p. 3 and Supplementary S1, p. 12

import Mathlib
import Definitions.Def_SupConGeometry_Basic

open Finset

namespace SupConGeometry

theorem supcon_loss_lower_bound {N K h b : ℕ} (hK : 2 ≤ K) (hKh : K ≤ h + 1) (hb : 3 ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (Z : Fin N → Rep h) (hZ : ∀ n, ‖Z n‖ = ρ)
    (Y : Fin N → Fin K) (hY : IsBalanced Y) :
    (∑ l ∈ Icc 2 b, (l : ℝ) * (batchCountTotal Y b l : ℝ) *
        Real.log ((l : ℝ) - 1 + ((b : ℝ) - l) *
          Real.exp (-((K : ℝ) * ρ ^ 2 / ((K : ℝ) - 1))))) ≤ scLoss Z Y b ∧
    (scLoss Z Y b =
        ∑ l ∈ Icc 2 b, (l : ℝ) * (batchCountTotal Y b l : ℝ) *
          Real.log ((l : ℝ) - 1 + ((b : ℝ) - l) *
            Real.exp (-((K : ℝ) * ρ ^ 2 / ((K : ℝ) - 1)))) ↔
      ∃ ζ : Fin K → Rep h, (∀ n, Z n = ζ (Y n)) ∧ IsSphereInscribedRegularSimplex ζ ρ) := by sorry

end SupConGeometry
