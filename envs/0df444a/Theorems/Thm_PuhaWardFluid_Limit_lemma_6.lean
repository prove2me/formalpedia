-- Prove2me | Theorems.Thm_PuhaWardFluid_Limit_lemma_6
-- name    : PuhaWardFluid.Limit.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:18.537412+00:00
-- url     : https://prove2.me/theorems/22369cda-dd8f-437f-973a-b85fe83cc44c
-- title:
--   Lemma 6, (61), p. 20 — ⟨1_[0,x] h^r_j, η^N_j(t)⟩ = ∫_0^{F^N_{j,t}(x)} h^r_j((F^N_{j,t})^{-1}(y)) dy
-- statement:
--   For each $N$, class $j$, $t\ge0$ and $x\in[0,H^r_j)$, let $F^N_{j,t}(x)=\langle 1_{[0,x]},\eta^N_j(t)\rangle$ be the number of class-$j$ potential customers at time $t$ with potential waiting time at most $x$, and $(F^N_{j,t})^{-1}(y)=\inf\{x\in\mathbb R_+:F^N_{j,t}(x)\ge y\}$. Then
--   $$\big\langle 1_{[0,x]}h^r_j,\eta^N_j(t)\big\rangle=\int_0^{F^N_{j,t}(x)}h^r_j\big((F^N_{j,t})^{-1}(y)\big)\,dy .\tag{61}$$
--
--   This alternative representation of the reneging compensator is what allows the limit of the reneging process to be identified with the nonlinear function (40) of the fluid model, even with batch arrivals.
--
--   **Formalization Note** Both sides are integrals of nonnegative functions computed in $[0,\infty]$; the identity holds on every sample path, since $\eta^N_j(t)$ is a finite sum of unit Dirac masses. $h^r_j(\infty):=0$, a value never used on a set of positive measure.
-- source:
--   Puha & Ward, Fluid limits for multiclass many-server queues with general reneging distributions and head-of-the-line scheduling, Math. Oper. Res., Articles in Advance (21 Dec 2021), doi:10.1287/moor.2021.1166, p. 20 (PDF 21), Lemma 6, (61)

import Mathlib
import Definitions.Def_PuhaWardFluid_Limit_Queue

open MeasureTheory
open scoped NNReal ENNReal

namespace PuhaWardFluid.Limit

/-- **Lemma 6, (61)** (p. 20). For each `N`, class `j`, `t ≥ 0` and `x ∈ [0, H^r_j)`, with
`F^N_{j,t}(x) = ⟨1_{[0,x]}, η^N_j(t)⟩`,
`⟨1_{[0,x]} h^r_j, η^N_j(t)⟩ = ∫_0^{F^N_{j,t}(x)} h^r_j((F^N_{j,t})^{-1}(y)) dy`
(both sides in `[0, ∞]`), on every sample path. -/
theorem lemma_6 {J : ℕ} (L : ClassLaws J) {Ω : Type*} (Q : QueueSeq J Ω) (N : ℕ+) (ω : Ω)
    (j : Fin J) (t : ℝ≥0) (x : ℝ) (hx0 : 0 ≤ x) (hxH : ENNReal.ofReal x < L.Hr j) :
    lpair ((Set.Iic x).indicator (L.hr j)) (Q.eta L N ω t j) =
      ∫⁻ y in Set.Icc (0 : ℝ) (Fcdf (Q.eta L N ω t j) x),
        hazardE (L.gr j) (FcdfInv (Q.eta L N ω t j) y) := by sorry

end PuhaWardFluid.Limit
