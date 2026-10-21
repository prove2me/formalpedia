-- Prove2me | Theorems.Thm_SyncQueues_WaitingTime_lemma_6_1
-- name    : SyncQueues.WaitingTime.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:52.221679+00:00
-- url     : https://prove2.me/theorems/aace87f2-6627-485b-990d-af320a4ea22a
-- title:
--   Lemma 6.1, p. 23 — truncating at r_n → ∞ generations costs nothing in L^p, for the queue and for the tree
-- statement:
--   Assume (3.5) for some $\beta>0$ (with $E[e^{\beta\chi}]<\infty$). For each $n\ge m$ let $W^{(n)}=\bigvee_{r\ge0}\hat U_r$ be the stationary waiting time of the $n$-server system, built on its own probability space, and let $W=\bigvee_{r\ge0}U_r$ be the endogenous solution (3.9) on the limit tree. Then for every sequence $r_n\to\infty$ and every $p\ge1$,
--   $$\lim_{n\to\infty}E\Big[\Big|W^{(n)}-\bigvee_{r=0}^{r_n}\hat U_r\Big|^p\Big]=0\qquad\text{and}\qquad \lim_{n\to\infty}E\Big[\Big|W-\bigvee_{r=0}^{r_n}U_r\Big|^p\Big]=0 .$$
--   In particular, writing $\mu_n$, $\hat\nu_k$, $\nu_k$, $\mu$ for the laws of $W^{(n)}$, $\bigvee_{r\le k}\hat U_r$, $\bigvee_{r\le k}U_r$ and $W$, the Wasserstein distances satisfy $W_p(\mu_n,\hat\nu_{r_n})\to0$ and $W_p(\nu_{r_n},\mu)\to0$.
--
--   These are the first and last terms of the triangle inequality (6.5) that proves the many-server limit.
--
--   **Formalization Note** For fixed job size, Assumption 3.1 (i) holds trivially and (ii) is (3.5), since $\lambda^*_n=\lambda m=\lambda^*$. Expectations of $|\cdot|^p$ are lower Lebesgue integrals in $[0,\infty]$, so they cannot vanish by default. $W_p$ is the published `WassersteinDRO.Duality.wassersteinDistance` on $\mathbb R$. The statement about $n$ only concerns $n\ge m$, where the system exists.
-- source:
--   Olvera-Cravioto & Ruiz-Lacedelli, arXiv:1501.00186v3, p. 23, Lemma 6.1 (with $\mu_n,\hat\nu_k,\nu_k,\mu$ defined above it, p. 23); proof pp. 24–25

import Mathlib
import Definitions.Def_SyncQueues_WaitingTime_BranchingTree
import Definitions.Def_SyncQueues_WaitingTime_Model
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

namespace SyncQueues.WaitingTime

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem lemma_6_1 {m : ℕ} (hm : 0 < m) {lam : ℝ} (hlam : 0 < lam)
    (Bm : Measure (Fin m → ℝ)) [IsProbabilityMeasure Bm] (hBm : ∀ᵐ x ∂Bm, ∀ i, 0 ≤ x i)
    {β : ℝ} (hβ : 0 < β)
    (hint : Integrable (fun x => Real.exp (β * x)) (pieceLaw Bm))
    (hstab : (m : ℝ) * (∫ x, Real.exp (β * x) ∂(pieceLaw Bm)) * (lam * m / (lam * m + β)) < 1)
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (E : ∀ n, ℕ → Ω n → ℝ) (R : ∀ n, ℕ → Ω n → (Fin m → ℕ)) (C : ∀ n, ℕ → Ω n → (Fin m → ℝ))
    (hsys : ∀ n, m ≤ n → IsSyncSystem (P n) m n lam Bm (E n) (R n) (C n))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (χ τ : List (Fin m) → Ω' → ℝ) (htree : IsLimitTree P' (pieceLaw Bm) (lam * m) χ τ)
    {p : ℝ} (hp : 1 ≤ p) (rn : ℕ → ℕ) (hrn : Tendsto rn atTop atTop) :
    Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal
        (|Wn (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) - UhatUpTo (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) (rn n)| ^ p) ∂(P n)) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal
        (|endoW χ τ ω - genMaxUpTo χ τ (rn n) ω| ^ p) ∂P') atTop (𝓝 0) ∧
    Tendsto (fun n => WassersteinDRO.Duality.wassersteinDistance p
        ((P n).map (fun ω => Wn (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω)))
        ((P n).map (fun ω => UhatUpTo (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) (rn n)))) atTop (𝓝 0) ∧
    Tendsto (fun n => WassersteinDRO.Duality.wassersteinDistance p
        (P'.map (fun ω => genMaxUpTo χ τ (rn n) ω)) (P'.map (fun ω => endoW χ τ ω)))
      atTop (𝓝 0) := by sorry

end SyncQueues.WaitingTime
