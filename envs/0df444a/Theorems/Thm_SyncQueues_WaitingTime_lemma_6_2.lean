-- Prove2me | Theorems.Thm_SyncQueues_WaitingTime_lemma_6_2
-- name    : SyncQueues.WaitingTime.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:59.438805+00:00
-- url     : https://prove2.me/theorems/96222e03-878b-4e4b-a605-70108f4aa9d5
-- title:
--   Lemma 6.2, p. 25 — the multi-labelled paths contribute at most (r/n) E[Ñ²] ρ_β^r
-- statement:
--   Fix $n\ge m$, $\beta>0$ and $r\ge1$. Let $M_r$ be the set of labels $\mathbf i$ at graph distance $r$ from the tagged job whose job carries some other label $\mathbf j\ne\mathbf i$ (the merged paths of the predecessor graph). Then
--   $$E\Big[\sum_{\mathbf i\in M_r}e^{\beta\hat S_{\mathbf i}}\Big]\;\le\;\frac rn\,E\big[\tilde N^2\big]\,(\tilde\rho_\beta)^r=\frac rn\,m^2\,\rho_\beta^{\,r},$$
--   where $\tilde\rho_\beta=E[\tilde N]E[e^{\beta(\chi-\tilde\tau)}]=m\,E[e^{\beta\chi}]\,\lambda m/(\lambda m+\beta)$ for job size $\tilde N\equiv m$.
--
--   The bound says that merging of paths, the only obstruction to the predecessor graph being a tree, is of order $1/n$; it drives the coupling of Proposition 6.4.
--
--   **Formalization Note** The other label $\mathbf j$ may have any length, as on the page. The expectation and $\rho_\beta$ are extended nonnegative reals, so no stability condition is assumed and the bound is meaningful when $E[e^{\beta\chi}]=\infty$.
-- source:
--   Olvera-Cravioto & Ruiz-Lacedelli, arXiv:1501.00186v3, p. 25, Lemma 6.2; proof pp. 25–27

import Mathlib
import Definitions.Def_SyncQueues_WaitingTime_BranchingTree
import Definitions.Def_SyncQueues_WaitingTime_Model

namespace SyncQueues.WaitingTime

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem lemma_6_2 {m : ℕ} (hm : 0 < m) {lam : ℝ} (hlam : 0 < lam)
    (Bm : Measure (Fin m → ℝ)) [IsProbabilityMeasure Bm] (hBm : ∀ᵐ x ∂Bm, ∀ i, 0 ≤ x i)
    {n : ℕ} (hn : m ≤ n)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℕ → Ω → ℝ) (R : ℕ → Ω → (Fin m → ℕ)) (C : ℕ → Ω → (Fin m → ℝ))
    (hsys : IsSyncSystem P m n lam Bm E R C)
    {β : ℝ} (hβ : 0 < β) {r : ℕ} (hr : 1 ≤ r) :
    ∫⁻ ω, ∑ v ∈ multiLabelled (fun k => R k ω) r,
        ENNReal.ofReal (Real.exp (β * pathSumHat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) (List.ofFn v))) ∂P ≤
      ENNReal.ofReal ((r : ℝ) / n * (m : ℝ) ^ 2) * rho Bm lam β ^ r := by sorry

end SyncQueues.WaitingTime
