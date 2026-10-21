-- Prove2me | Theorems.Thm_SyncQueues_WaitingTime_theorem_3_2_stability
-- name    : SyncQueues.WaitingTime.theorem_3_2_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:00.489094+00:00
-- url     : https://prove2.me/theorems/800b049c-56d9-408a-ac8f-f43791b48b50
-- title:
--   Theorem 3.2 (stability part), p. 13 — under (3.5), W^(n,t0) → W^(n) < ∞ a.s. as t0 → −∞
-- statement:
--   This is the first half of the paper's main theorem: under the stability condition, the waiting time of the tagged job has an almost surely finite limit as the empty starting time recedes to $-\infty$.
--
--   Fix $n\ge m$. Suppose that for some $\beta>0$, $E[e^{\beta\chi}]<\infty$ and
--   $$m\,E\big[e^{\beta\chi}\big]\,\frac{\lambda m}{\lambda m+\beta}<1,\tag{3.5}$$
--   where $\chi\sim B$; this is $E[\hat N]\,E[e^{\beta(\chi-\hat\tau)}]<1$ with $\hat N\equiv m$ and $\hat\tau\sim\mathrm{Exp}(\lambda^*_n)$, $\lambda^*_n=\lambda m$. Then almost surely the generation maxima $\hat U_r$ of the predecessor graph are bounded above, and
--   $$\lim_{t_0\to-\infty}W^{(n,t_0)}_\emptyset=W^{(n)}=\bigvee_{r\ge0}\hat U_r<\infty .$$
--
--   By Loynes' lemma and Palm theory this is the stability of the $n$-server network; $W^{(n)}$ is its stationary waiting time.
--
--   **Formalization Note** The finiteness $E[e^{\beta\chi}]<\infty$, implicit on the page inside "$<1$", is a separate hypothesis: without it the Bochner integral of a non-integrable function is $0$ and (3.5) would hold vacuously. Boundedness of the $\hat U_r$ is stated so that the real supremum defining $W^{(n)}$ is the true one.
-- source:
--   Olvera-Cravioto & Ruiz-Lacedelli, arXiv:1501.00186v3, p. 13, Theorem 3.2, first part ((3.5) and the a.s. limit); proof pp. 21–23

import Mathlib
import Definitions.Def_SyncQueues_WaitingTime_BranchingTree
import Definitions.Def_SyncQueues_WaitingTime_Model

namespace SyncQueues.WaitingTime

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem theorem_3_2_stability {m : ℕ} (hm : 0 < m) {lam : ℝ} (hlam : 0 < lam)
    (Bm : Measure (Fin m → ℝ)) [IsProbabilityMeasure Bm] (hBm : ∀ᵐ x ∂Bm, ∀ i, 0 ≤ x i)
    {β : ℝ} (hβ : 0 < β)
    (hint : Integrable (fun x => Real.exp (β * x)) (pieceLaw Bm))
    (hstab : (m : ℝ) * (∫ x, Real.exp (β * x) ∂(pieceLaw Bm)) * (lam * m / (lam * m + β)) < 1)
    {n : ℕ} (hn : m ≤ n)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℕ → Ω → ℝ) (R : ℕ → Ω → (Fin m → ℕ)) (C : ℕ → Ω → (Fin m → ℝ))
    (hsys : IsSyncSystem P m n lam Bm E R C) :
    ∀ᵐ ω ∂P,
      BddAbove (Set.range fun r => Uhat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) r) ∧
      Tendsto (fun t0 => waitT (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) t0) atBot (𝓝 (Wn (fun k => E k ω) (fun k => R k ω) (fun k => C k ω))) := by sorry

end SyncQueues.WaitingTime
