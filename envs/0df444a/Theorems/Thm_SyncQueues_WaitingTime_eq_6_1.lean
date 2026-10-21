-- Prove2me | Theorems.Thm_SyncQueues_WaitingTime_eq_6_1
-- name    : SyncQueues.WaitingTime.eq_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:37.96593+00:00
-- url     : https://prove2.me/theorems/6093097b-8ace-43e3-9b46-87faa97ce5ab
-- title:
--   Proof of Theorem 3.2 (Stability), (6.1), p. 21 — W^(n,t0) increases to ⋁_r Û_r as t0 → −∞
-- statement:
--   This is the first step of the stability proof: the waiting time of the tagged job, started from an empty system, increases to the maximum over the whole predecessor graph as the starting time recedes.
--
--   Fix $n\ge m$. $W^{(n,t_0)}_\emptyset$ is the waiting time of the tagged job when the system is empty at time $t_0<0$, and $\hat U_r$ is the maximum of the path sums $\hat S_{\mathbf j}$ over the labels at graph distance $r$ from the tagged job in $\mathcal G_n(-\infty)$. Then almost surely $t_0\mapsto W^{(n,t_0)}_\emptyset$ is non-increasing on $(-\infty,0)$ and
--   $$\lim_{t_0\to-\infty}W^{(n,t_0)}_\emptyset=\bigvee_{r=0}^\infty\hat U_r\;\triangleq\;W^{(n)}\qquad\text{in }[0,\infty].$$
--
--   No stability condition is needed: the limit may be $+\infty$. Finiteness is the content of the stability part of Theorem 3.2.
--
--   **Formalization Note** The limit is taken in the extended reals `EReal`, so that the case $W^{(n)}=+\infty$ is represented and not replaced by a junk value. Monotonicity is stated on $t_0<0$, the page's range.
-- source:
--   Olvera-Cravioto & Ruiz-Lacedelli, arXiv:1501.00186v3, p. 21, proof of Theorem 3.2 (Stability), (6.1) and the display after it; (3.1)–(3.2), pp. 10–11

import Mathlib
import Definitions.Def_SyncQueues_WaitingTime_BranchingTree
import Definitions.Def_SyncQueues_WaitingTime_Model

namespace SyncQueues.WaitingTime

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem eq_6_1 {m : ℕ} (hm : 0 < m) {lam : ℝ} (hlam : 0 < lam)
    (Bm : Measure (Fin m → ℝ)) [IsProbabilityMeasure Bm] (hBm : ∀ᵐ x ∂Bm, ∀ i, 0 ≤ x i)
    {n : ℕ} (hn : m ≤ n)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℕ → Ω → ℝ) (R : ℕ → Ω → (Fin m → ℕ)) (C : ℕ → Ω → (Fin m → ℝ))
    (hsys : IsSyncSystem P m n lam Bm E R C) :
    ∀ᵐ ω ∂P,
      AntitoneOn (fun t0 => waitT (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) t0) (Set.Iio 0) ∧
      Tendsto (fun t0 => ((waitT (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) t0 : ℝ) : EReal)) atBot
        (𝓝 (⨆ r : ℕ, ((Uhat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) r : ℝ) : EReal))) := by sorry

end SyncQueues.WaitingTime
