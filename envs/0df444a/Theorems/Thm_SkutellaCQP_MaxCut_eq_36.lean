-- Prove2me | Theorems.Thm_SkutellaCQP_MaxCut_eq_36
-- name    : SkutellaCQP.MaxCut.eq_36
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:11.392093+00:00
-- url     : https://prove2.me/theorems/4a2a71df-d133-4c18-9eb6-b5ef90b0edad
-- title:
--   (36), p. 30 — c(E_J) = Σⱼ wⱼCⱼ − Σⱼ wⱼpⱼ + c(E_cut) for every partition of J into m machines
-- statement:
--   Consider $n$ jobs with processing times $p_j>0$ and weights $w_j\ge0$ on $m\ge1$ identical parallel machines, Smith's order $\prec$, and the weighted complete graph $G_J$ with $c(jk)=w_jp_k$ for $k\prec j$. Let $\sigma$ be any assignment of the jobs to the machines (a partition $J_1,\dots,J_m$), let $C_j$ be the completion times of the schedule that sequences each machine by $\prec$, and let $E_{\mathrm{cut}}$ be the $m$-cut induced by the partition. Then
--   $$
--   c(E_J)=\sum_j w_jC_j-\sum_j w_jp_j+c(E_{\mathrm{cut}}).
--   $$
--
--   The value of a schedule is the weight of the edges inside the parts plus the constant $\sum_j w_jp_j$. Since $c(E_J)$ and $\sum_jw_jp_j$ do not depend on $\sigma$, minimizing $\sum_jw_jC_j$ is the same as maximizing the weight of the induced $m$-cut; this is the reduction of $Pm\,|\,|\sum w_jC_j$ to Max-$m$-Cut.
--
--   **Formalization Note** The identity holds for any real data; the standing hypotheses $p>0$, $w\ge0$, $m>0$ are kept for uniformity with the other statements of the mission.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 30, §6, display (36)

import Mathlib
import Definitions.Def_SkutellaCQP_MaxCut_Setting

namespace SkutellaCQP.MaxCut

open Finset

/-- Display (36), §6, p. 30. For every partition of the jobs `J` into `m` subsets, given by an
assignment `σ`, the total weight of `G_J` equals the value of the corresponding schedule minus
`∑_j w_j p_j` plus the weight of the induced `m`-cut:
`c(E_J) = ∑_j w_j C_j − ∑_j w_j p_j + c(E_cut)`. -/
theorem eq_36 {m n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j) (hm : 0 < m) :
    ∀ σ : Fin n → Fin m, cE p w = val p w σ - ∑ j, w j * p j + cut p w σ := by sorry

end SkutellaCQP.MaxCut
