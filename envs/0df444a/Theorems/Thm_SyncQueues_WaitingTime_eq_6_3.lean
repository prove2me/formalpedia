-- Prove2me | Theorems.Thm_SyncQueues_WaitingTime_eq_6_3
-- name    : SyncQueues.WaitingTime.eq_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:54.551906+00:00
-- url     : https://prove2.me/theorems/400ee360-75d2-4dbd-90c4-3add17c72fec
-- title:
--   (6.2)–(6.4), pp. 21–23 — P(Û_r > 0) ≤ E[Σ_{j∈Â_r} e^{βŜ_j}] ≤ (m E[e^{β(χ−τ)}])^r
-- statement:
--   This is the key estimate of the stability proof: the predecessor graph is dominated, path by path, by the weighted branching tree.
--
--   Fix $n\ge m$, $\beta>0$ and $r\ge0$. With $\hat U_r=\max_{\mathbf j\in\hat A_r}\hat S_{\mathbf j}$ the maximal path sum at graph distance $r$ from the tagged job,
--   $$P\big(\hat U_r>0\big)\;\le\;E\Big[\sum_{\mathbf j\in\hat A_r}e^{\beta\hat S_{\mathbf j}}\Big]\;\le\;\Big(m\,E\big[e^{\beta\chi}\big]\,\frac{\lambda m}{\lambda m+\beta}\Big)^r=\rho_\beta^{\,r}.$$
--   The first inequality is Markov's; the second is (6.3) combined with the tree computation (6.4). Under (3.5), $\rho_\beta<1$, which gives (6.2) with $c=\rho_\beta$, and Borel–Cantelli then shows that $\hat U_r>0$ only finitely often.
--
--   **Formalization Note** The expectations are extended nonnegative reals, so the statement is meaningful (and the right side infinite) when $E[e^{\beta\chi}]=\infty$; no stability condition is assumed. The tagged job is the first arrival after $0$, so the inter-arrival times on its own edges are $T_1$ plus an $\mathrm{Exp}(\lambda m)$ variable, which only decreases the left side.
-- source:
--   Olvera-Cravioto & Ruiz-Lacedelli, arXiv:1501.00186v3, p. 21, (6.2); pp. 22–23, the Markov bound and (6.3)–(6.4)

import Mathlib
import Definitions.Def_SyncQueues_WaitingTime_BranchingTree
import Definitions.Def_SyncQueues_WaitingTime_Model

namespace SyncQueues.WaitingTime

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem eq_6_3 {m : ℕ} (hm : 0 < m) {lam : ℝ} (hlam : 0 < lam)
    (Bm : Measure (Fin m → ℝ)) [IsProbabilityMeasure Bm] (hBm : ∀ᵐ x ∂Bm, ∀ i, 0 ≤ x i)
    {n : ℕ} (hn : m ≤ n)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℕ → Ω → ℝ) (R : ℕ → Ω → (Fin m → ℕ)) (C : ℕ → Ω → (Fin m → ℝ))
    (hsys : IsSyncSystem P m n lam Bm E R C)
    {β : ℝ} (hβ : 0 < β) (r : ℕ) :
    P {ω | 0 < Uhat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) r} ≤
        ∫⁻ ω, ∑ v : Fin r → Fin m,
          ENNReal.ofReal (Real.exp (β * pathSumHat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) (List.ofFn v))) ∂P ∧
      ∫⁻ ω, ∑ v : Fin r → Fin m,
          ENNReal.ofReal (Real.exp (β * pathSumHat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) (List.ofFn v))) ∂P ≤
        rho Bm lam β ^ r := by sorry

end SyncQueues.WaitingTime
