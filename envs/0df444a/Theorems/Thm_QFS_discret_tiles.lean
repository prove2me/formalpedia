-- Prove2me | Theorems.Thm_QFS_discret_tiles
-- name    : QFS.discret_tiles
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-07T09:00:27.515958+00:00
-- url     : https://prove2.me/theorems/375707ae-ba39-4200-be9d-85cdca1efe1c
-- title:
--   Equation (15) — the discrete inequality with both sides integrated over the tiles
-- statement:
--   **Display (15) of Bux–Kassmann–Schulze**, in §3.2. **This statement is not yet proved — it is
--   an open target of this mission.**
--
--   For $d \ge 1$, $\vartheta > 0$, $\Lambda \ge 1$ and $\alpha \in (0,2)$ there are $\kappa \ge 1$
--   and $c > 0$ such that: for every $\vartheta$-bounded $\Gamma$, every spacing $h > 0$, every
--   kernel $k$ whose discretisation $\omega^k_h$ satisfies assumption (4) on $h\mathbb{Z}^d$ beyond
--   separation $\sqrt d\,h$, every ball $B = B_R(x_0)$ and every $f$,
--
--   $$c\!\!\sum_{\substack{x,y \in B \cap h\mathbb{Z}^d\\ \lVert x-y\rVert > \sqrt d h}}\!\!
--   (f(x)-f(y))^2\!\!\iint_{A_h(x)\times A_h(y)}\!\!\lVert s-t\rVert^{-d-\alpha}\,d(s,t)
--   \;\le\!\!\sum_{\substack{x,y \in B^* \cap h\mathbb{Z}^d\\ \lVert x-y\rVert > \sqrt d h}}\!\!
--   (f(x)-f(y))^2\!\!\iint_{A_h(x)\times A_h(y)}\!\! k(s,t)\,d(s,t),$$
--
--   where $B^* = B_{\kappa R}(x_0)$ and $A_h(u)$ is the open cube of edge $h$ at $u$. Both sides are
--   sums over **ordered** pairs, so each unordered pair contributes twice, and both are lower
--   Lebesgue integrals in $[0,\infty]$.
--
--   **What makes this (15) rather than Corollary 3.1.** The source reaches (15) by converting *both*
--   sides of Corollary 3.1 from the kernel evaluated at the lattice points to the kernel **integrated
--   over the pair of tiles**, quoting Lemma 3.4 for the comparison. This mission already carries
--   `QFS.discret_lintegral`, which converts only the right-hand side — it must, since $\omega^k_h$
--   *is* the tile average of $k$ — and keeps the left in Corollary 3.1's own form with
--   $\lVert x-y\rVert^{-d-\alpha}$ at the lattice points, because Fatou applies to it directly and
--   that avoids one appeal to Lemma 3.4. That variant is what the development's proof of Theorem 1.1
--   uses; the display above is what the source actually prints, and it is stated here so that the
--   paper's own step is on the platform.
--
--   **Route to a proof.** Corollary 3.1 (`QFS.corollaryThreeOne`) with $R_0 = \sqrt d$ gives the
--   inequality with $\omega^k_h$ on the right and the jump kernel at the lattice points on the left.
--   The right-hand tile integral is exactly $h^{2d}\,\omega^k_h(x,y)$, by the definition of
--   `QFS.discreteKernel`. For the left, Lemma 3.4 on $h\mathbb{Z}^d$ (`QFS.lemma_cubes`) gives
--   $\lVert s-t\rVert > \lVert x-y\rVert/(2\sqrt d)$ for $s \in A_h(x)$, $t \in A_h(y)$, hence
--   $\iint \le h^{2d}(2\sqrt d)^{d+\alpha}\lVert x-y\rVert^{-d-\alpha}$. The two factors of $h^{2d}$
--   cancel and $c$ differs from Corollary 3.1's by $(2\sqrt d)^{-(d+\alpha)}$ — a factor depending
--   only on the dimension once $\alpha < 2$ is used, which is the source's "a constant that differs
--   from the one above by a factor only depending on the dimension $d$".
--
--   The separation threshold $\sqrt d\,h$ is the Euclidean diameter of a cube of edge $h$, so the two
--   cubes are disjoint. No measurability of $k$ is assumed, and $\Gamma$ enters only through
--   assumption (4) for $\omega^k_h$.
-- source:
--   https://arxiv.org/abs/1707.09277

import Definitions.Def_QFS_Section3Kernel
import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Definitions.Def_QFS_ConeGap
import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Section4
import Definitions.Def_QFS_Cubes
import Definitions.Def_QFS_Section3
import Definitions.Def_QFS_Section5
import Definitions.Def_QFS_Section1
import Definitions.Def_QFS_ThinCones
import Definitions.Def_QFS_Renormalization
import Definitions.Def_QFS_FirstJump
import Definitions.Def_QFS_Assembly
import Definitions.Def_QFS_PathAssembly
import Definitions.Def_QFS_BlockPaths
import Definitions.Def_QFS_Section6
import Definitions.Def_QFS_Rescaling
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Real Set Metric ENNReal

open QFS

variable {d : ℕ}

theorem QFS.discret_tiles (ϑ Λ α : ℝ) (hd : 0 < d) (hϑ : 0 < ϑ) (hΛ : 1 ≤ Λ) (hα : 0 < α)
    (hα2 : α < 2) :
    ∃ κ c : ℝ, 1 ≤ κ ∧ 0 < c ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      ∀ h : ℝ, 0 < h →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
        DiscreteKernelBounds Γ α Λ (Real.sqrt d * h) (scaledLattice d h)
          (discreteKernel d k h) →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ),
        0 < R →
        ENNReal.ofReal c *
            discreteFormOn (scaledLattice d h) (ball x₀ R) (Real.sqrt d * h)
              (fun x y => ∫⁻ q in cube h x ×ˢ cube h y, jumpKernel d α q.1 q.2) f
          ≤ discreteFormOn (scaledLattice d h) (ball x₀ (κ * R)) (Real.sqrt d * h)
              (fun x y => ∫⁻ q in cube h x ×ˢ cube h y, k q.1 q.2) f := by sorry
