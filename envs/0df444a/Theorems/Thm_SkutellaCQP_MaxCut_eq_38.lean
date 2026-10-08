-- Prove2me | Theorems.Thm_SkutellaCQP_MaxCut_eq_38
-- name    : SkutellaCQP.MaxCut.eq_38
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:09.885572+00:00
-- url     : https://prove2.me/theorems/ada21ead-520f-4d81-8432-3e1c59aef990
-- title:
--   (38), p. 31 — Z*_cut ≤ (m − 1)/m · c(E_J) + (1/2 − 1/(2m)) Σⱼ wⱼpⱼ
-- statement:
--   Consider $n$ jobs with processing times $p_j>0$ and weights $w_j\ge0$ on $m\ge1$ identical parallel machines and the weighted complete graph $G_J$ of total weight $c(E_J)$. Every $m$-cut of $G_J$, induced by a partition $J_1,\dots,J_m$ of the jobs, has weight
--   $$
--   c(E_{\mathrm{cut}})\le\frac{m-1}{m}\,c(E_J)+\Big(\frac12-\frac1{2m}\Big)\sum_j w_jp_j .
--   $$
--   In particular this bounds the weight $Z^*_{\mathrm{cut}}$ of a maximum $m$-cut.
--
--   The bound compares the maximum cut with the scheduling optimum and is the step that turns a $\rho$-approximate cut into an approximate schedule in Theorem 6.1.
--
--   **Formalization Note** $Z^*_{\mathrm{cut}}$ is not a primitive; the bound is stated for every partition, which is equivalent because there are finitely many.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 31, §6, proof of Theorem 6.1, display (38)

import Mathlib
import Definitions.Def_SkutellaCQP_MaxCut_Setting

namespace SkutellaCQP.MaxCut

open Finset

/-- Display (38), §6, proof of Theorem 6.1, p. 31. Every `m`-cut of `G_J` (hence a maximum one,
`Z*_cut`) weighs at most `(m − 1)/m · c(E_J) + (1/2 − 1/(2m)) ∑_j w_j p_j`. -/
theorem eq_38 {m n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j) (hm : 0 < m) :
    ∀ τ : Fin n → Fin m,
      cut p w τ ≤ ((m : ℝ) - 1) / m * cE p w + (1 / 2 - 1 / (2 * (m : ℝ))) *
        ∑ j, w j * p j := by sorry

end SkutellaCQP.MaxCut
