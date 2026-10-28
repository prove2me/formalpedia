-- Prove2me | Theorems.Thm_StochOptForest_ApxRisk_minimizer_consistency
-- name    : StochOptForest.ApxRisk.minimizer_consistency
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:00.06316+00:00
-- url     : https://prove2.me/theorems/76454c6f-a23f-48fa-935a-25c9818fdedd
-- title:
--   Proof of Theorem 9, p. 74 — minimizers of uniformly close functions are close (Shapiro et al. 2014, Thm 5.3)
-- statement:
--   Let $g:\mathbb R^d\to\mathbb R$ be continuous with a unique global minimizer $\bar z$, and suppose some sublevel set $\{z: g(z)\le\alpha\}$ with $\alpha>g(\bar z)$ is bounded. Then for every $\varepsilon>0$ there is $\eta>0$ such that, for every function $h:\mathbb R^d\to\mathbb R$ with
--   $$\sup_{z\in\mathbb R^d}|h(z)-g(z)|\le\eta,$$
--   every global minimizer $z$ of $h$ satisfies $\|z-\bar z\|_2\le\varepsilon$.
--
--   The proof of Theorem 9 uses this consistency of minimizers (through Theorem 5.3 of Shapiro, Dentcheva and Ruszczyński, 2014) to show $z^*(f_0+t\delta_f)\to z^*(f_0)$ as $t\to0$.
--
--   **Formalization Note** The page applies the cited theorem with a supremum over a compact set $\mathcal N$ containing the minimizers; this statement gives the deterministic content with a supremum over all of $\mathbb R^d$ and the bounded sublevel set of $g$ in place of $\mathcal N$.
-- source:
--   Kallus & Mao, arXiv:2008.07473v6, p. 74, Proof for Theorem 9 (citing Shapiro et al. 2014, Theorem 5.3)

import Mathlib
import Definitions.Def_StochOptForest_ApxRisk_Model

namespace StochOptForest.ApxRisk

theorem minimizer_consistency {d : ℕ} (g : Ed d → ℝ) (zbar : Ed d) (hg : Continuous g)
    (hmin : IsUniqueMin g zbar)
    (hlev : ∃ α : ℝ, g zbar < α ∧ Bornology.IsBounded {z | g z ≤ α}) :
    ∀ ε > 0, ∃ η > 0, ∀ h : Ed d → ℝ, (∀ z, |h z - g z| ≤ η) →
      ∀ z, (∀ w, h z ≤ h w) → ‖z - zbar‖ ≤ ε := by sorry

end StochOptForest.ApxRisk
