-- Prove2me | Theorems.Thm_SyncQueues_WaitingTime_proposition_6_4
-- name    : SyncQueues.WaitingTime.proposition_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:58.517986+00:00
-- url     : https://prove2.me/theorems/eed5d539-ae0a-4edd-bfe9-66e780207ccf
-- title:
--   Proposition 6.4, p. 27 — W_p(ν̂_{r_n}, ν̃_{r_n}) → 0: the truncated predecessor graph couples with the weighted branching tree
-- statement:
--   Assume (3.5) for some $\beta>0$ (with $E[e^{\beta\chi}]<\infty$). Let $\hat\nu_k$ be the law of $\bigvee_{r=0}^k\hat U_r$ in the $n$-server system and $\tilde\nu_k$ the law of $\bigvee_{r=0}^k\tilde U_r$ on the weighted branching tree. Then for every sequence $r_n\to\infty$ and every $p\ge1$,
--   $$W_p\big(\hat\nu_{r_n},\tilde\nu_{r_n}\big)\longrightarrow0,\qquad n\to\infty .$$
--
--   This is the main coupling of the paper, between the predecessor graph truncated at distance $r_n$ and its tree approximation; it is the middle term of (6.5).
--
--   **Formalization Note** For fixed job size the tilde tree (job sizes $\tilde N\sim f_n$, $\tilde\tau\sim\mathrm{Exp}(\lambda^*_n)$) is the limit tree itself, because $f_n=f=\delta_m$ and $\lambda^*_n=\lambda^*=\lambda m$; so $\tilde\nu_k$ is the law of $\bigvee_{r\le k}U_r$ on the tree of the definitions file, and Proposition 6.5 is not needed. Assumption 3.1 reduces to (3.5). $W_p$ is the published `WassersteinDRO.Duality.wassersteinDistance` on $\mathbb R$.
-- source:
--   Olvera-Cravioto & Ruiz-Lacedelli, arXiv:1501.00186v3, p. 27, Proposition 6.4; proof pp. 27–29

import Mathlib
import Definitions.Def_SyncQueues_WaitingTime_BranchingTree
import Definitions.Def_SyncQueues_WaitingTime_Model
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

namespace SyncQueues.WaitingTime

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem proposition_6_4 {m : ℕ} (hm : 0 < m) {lam : ℝ} (hlam : 0 < lam)
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
    Tendsto (fun n => WassersteinDRO.Duality.wassersteinDistance p
        ((P n).map (fun ω => UhatUpTo (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) (rn n)))
        (P'.map (fun ω => genMaxUpTo χ τ (rn n) ω))) atTop (𝓝 0) := by sorry

end SyncQueues.WaitingTime
