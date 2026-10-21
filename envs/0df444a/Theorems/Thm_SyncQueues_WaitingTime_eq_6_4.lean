-- Prove2me | Theorems.Thm_SyncQueues_WaitingTime_eq_6_4
-- name    : SyncQueues.WaitingTime.eq_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:32.484112+00:00
-- url     : https://prove2.me/theorems/af990364-19f7-45c5-8d36-4534ed2590cf
-- title:
--   (6.4), p. 23 — on the m-ary weighted branching tree, E[Σ_{|j|=r} e^{βS_j}] = (m E[e^{β(χ−τ)}])^r
-- statement:
--   On the $m$-ary weighted branching tree with i.i.d. edge marks $(\chi_{\mathbf j},\tau_{\mathbf j})$, $\chi\sim B$, $\tau\sim\mathrm{Exp}(\lambda^*)$ independent, $\lambda^*=\lambda m$, and for every $\beta>0$ and every generation $r\ge0$,
--   $$E\Big[\sum_{\mathbf j\in A_r}e^{\beta S_{\mathbf j}}\Big]=\Big(m\,E\big[e^{\beta(\chi-\tau)}\big]\Big)^r=\Big(m\,E\big[e^{\beta\chi}\big]\,\frac{\lambda m}{\lambda m+\beta}\Big)^r=\rho_\beta^{\,r},$$
--   where $A_r$ is the set of the $m^r$ nodes of generation $r$ and $S_{\mathbf j}$ is the sum of $\chi-\tau$ along the path from the root to $\mathbf j$. This is the standard first-moment computation for weighted branching processes, specialised to $\tilde N\equiv m$.
--
--   It is the quantity that the predecessor graph is compared with in (6.3), and the reason why $\rho_\beta<1$ is the stability condition.
--
--   **Formalization Note** Both sides are extended nonnegative reals, so the identity also holds when $E[e^{\beta\chi}]=\infty$ (both sides are then $+\infty$ for $r\ge1$).
-- source:
--   Olvera-Cravioto & Ruiz-Lacedelli, arXiv:1501.00186v3, p. 23, (6.4), with $\tilde N\equiv m$ and $\tilde\tau\sim\mathrm{Exp}(\lambda m)$ (§6 notation, p. 21)

import Mathlib
import Definitions.Def_SyncQueues_WaitingTime_BranchingTree
import Definitions.Def_SyncQueues_WaitingTime_Model

namespace SyncQueues.WaitingTime

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem eq_6_4 {m : ℕ} (hm : 0 < m) {lam : ℝ} (hlam : 0 < lam)
    (Bm : Measure (Fin m → ℝ)) [IsProbabilityMeasure Bm] (hBm : ∀ᵐ x ∂Bm, ∀ i, 0 ≤ x i)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (χ τ : List (Fin m) → Ω' → ℝ) (htree : IsLimitTree P' (pieceLaw Bm) (lam * m) χ τ)
    {β : ℝ} (hβ : 0 < β) (r : ℕ) :
    ∫⁻ ω, ∑ v : Fin r → Fin m,
        ENNReal.ofReal (Real.exp (β * pathSum χ τ (List.ofFn v) ω)) ∂P' =
      rho Bm lam β ^ r := by sorry

end SyncQueues.WaitingTime
