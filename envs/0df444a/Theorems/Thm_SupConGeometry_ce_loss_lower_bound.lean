-- Prove2me | Theorems.Thm_SupConGeometry_ce_loss_lower_bound
-- name    : SupConGeometry.ce_loss_lower_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T01:13:34.145354+00:00
-- url     : https://prove2.me/theorems/a1c25001-0c18-4ffd-b328-84d9fc461dcc
-- title:
--   Theorem 1 (as proved): cross-entropy lower bound and its equality case for $W\neq0$
-- statement:
--   Let $h,N,K\in\mathbb N$ with $2\le K\le h+1$ and $N\ge1$, let $\rho>0$, and let $z_1,\dots,z_N\in\mathbb R^h$ with $\|z_n\|\le\rho$, with balanced labels $Y\in[K]^N$. Let $W\in\mathbb R^{K\times h}$ have rows $w_y$. Then
--
--   $$\mathcal L_{CE}(Z,W;Y)\ \ge\ \log\Big(1+(K-1)\exp\Big(-\rho\frac{\sqrt K}{K-1}\|W\|_F\Big)\Big).$$
--
--   If moreover $W\neq0$, equality holds if and only if there are $\zeta_1,\dots,\zeta_K\in\mathbb R^h$ such that
--   1. (C1) $z_n=\zeta_{y_n}$ for all $n$;
--   2. (C2) $\{\zeta_y\}_y$ form a $\rho$-sphere-inscribed regular simplex;
--   3. (C3) there is $\rho_W>0$ with $w_y=\frac{\rho_W}{\rho}\zeta_y$ for all $y$.
--
--   **Formalization Note** The paper states the equality characterisation for every $W$. It fails at $W=0$: then $\mathcal L_{CE}=\log K$ equals the bound for every $Z$, while (C3) is impossible. The proof's case "$w_{y_n}=0$ gives $\zeta_{y_n}=0$" contradicts (S2). The statement is what the proof establishes: the bound for all $W$ and the characterisation for $W\neq0$. $N\ge1$ and $K\ge2$ are implicit in the factors $1/N$ and $1/(K-1)$.
-- source:
--   Graf, Hofer, Niethammer and Kwitt, Dissecting Supervised Contrastive Learning, ICML 2021, arXiv:2102.08817v4, Section 3.1, Theorem 1, p. 4; proof in Supplementary S2, pp. 30-33; standing assumption K ≤ h+1 of Supplementary S2, p. 28

import Mathlib
import Definitions.Def_SupConGeometry_Basic

open Finset

namespace SupConGeometry

theorem ce_loss_lower_bound {N K h : ℕ} (hK : 2 ≤ K) (hKh : K ≤ h + 1) (hN : 0 < N)
    (ρ : ℝ) (hρ : 0 < ρ) (Z : Fin N → Rep h) (hZ : ∀ n, ‖Z n‖ ≤ ρ) (W : Fin K → Rep h)
    (Y : Fin N → Fin K) (hY : IsBalanced Y) :
    Real.log (1 + ((K : ℝ) - 1) *
        Real.exp (-(ρ * (Real.sqrt K / ((K : ℝ) - 1)) * frobNorm W))) ≤ ceLoss Z W Y ∧
    (W ≠ 0 →
      (ceLoss Z W Y = Real.log (1 + ((K : ℝ) - 1) *
          Real.exp (-(ρ * (Real.sqrt K / ((K : ℝ) - 1)) * frobNorm W))) ↔
        ∃ ζ : Fin K → Rep h, (∀ n, Z n = ζ (Y n)) ∧ IsSphereInscribedRegularSimplex ζ ρ ∧
          ∃ ρW : ℝ, 0 < ρW ∧ ∀ y, W y = (ρW / ρ) • ζ y)) := by sorry

end SupConGeometry
