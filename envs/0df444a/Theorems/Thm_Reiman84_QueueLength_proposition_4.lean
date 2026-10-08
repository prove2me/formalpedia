-- Prove2me | Theorems.Thm_Reiman84_QueueLength_proposition_4
-- name    : Reiman84.QueueLength.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:06:43.26321+00:00
-- url     : https://prove2.me/theorems/366195cb-a013-4222-9b85-84b861186470
-- title:
--   Proposition 4 — n⁻¹Iⁿ_k(n) → 0 in probability
-- statement:
--   Consider a sequence of networks of §2 satisfying (20)–(26) and let $(Q^n,B^n)$ solve (1)–(3) almost surely, with cumulative idleness $I^n_k(t)=t-B^n_k(t)$. Then for $1\le k\le K$
--   $$n^{-1}I^n_k(n)\xrightarrow{P}0\qquad\text{as } n\to\infty,\qquad(30)$$
--   i.e. for every $\delta>0$, $P^n\{|n^{-1}I^n_k(n)|\ge\delta\}\to0$.
--
--   In heavy traffic each server is idle only a vanishing fraction of the time; this is what makes the random time change $B^n_k(n\,\cdot)/n$ converge to the identity.
-- source:
--   Reiman, Open Queueing Networks in Heavy Traffic, Math. Oper. Res. 9(3) (1984), p. 450, Proposition 4 (Eq. (30), p. 447)

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_Reiman84_QueueLength_Network
import Definitions.Def_Reiman84_QueueLength_HeavyTraffic

namespace Reiman84.QueueLength

open Filter Topology MeasureTheory

/-- Proposition 4, p. 450 (Eq. (30)): under (20)–(26), `n⁻¹ Iⁿ_k(n) → 0` in probability as
`n → ∞`, for each station `k`, where `Iⁿ_k(t) = t − Bⁿ_k(t)` is the cumulative idleness. -/
theorem proposition_4 {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)} (net : ∀ n, Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ)
    (hA : HeavyTrafficAssumptions net R mu s lam a c)
    (Q B : ∀ n, Ω n → ℝ → Fin K → ℝ)
    (hQ : ∀ n, ∀ᵐ ω ∂(P n), (net n).IsQueueSolution ω (Q n ω) (B n ω)) :
    ∀ k : Fin K, ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n : ℕ => P n {ω | δ ≤ |(n : ℝ)⁻¹ * Network.idle (B n ω) n k|})
        atTop (𝓝 0) := by sorry

end Reiman84.QueueLength
