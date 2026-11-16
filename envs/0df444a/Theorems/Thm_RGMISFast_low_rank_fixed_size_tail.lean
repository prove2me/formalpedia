-- Prove2me | Theorems.Thm_RGMISFast_low_rank_fixed_size_tail
-- name    : RGMISFast.low_rank_fixed_size_tail
-- status  : Proved
-- author  : @srikkanthr
-- created : 2026-11-15T22:17:25.232729+00:00
-- url     : https://prove2.me/theorems/784af4a0-5375-47ee-92a7-6e1ed25b1b1c
-- title:
--   Appendix A fixed-size tail for low-rank extensions
-- statement:
--   Let the graph have maximum degree at most $\Delta\ge2$, with a fixed root and independent exponential ranks of mean one. For integers $j\ge0$ and $k\ge1$, the probability that some root-connected seed of size $j+1$ has at least $k$ reachable low-rank vertices outside it is bounded by
--   $$
--   \Pr\left[\exists A:\ |A|=j+1,\ |\Gamma_{<a_M}(A)|\ge k\right]\le(8\Delta)^j2^{-k}.
--   $$
--   This is the fixed-size estimate in the proof of Lemma A.1. The seed is allowed to depend on the ranks and need not be active.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, Appendix A, proof of Lemma A.1, “A fixed size”, printed pp.29–30 (PDF pp.31–32), manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664. The displayed probability bound immediately before “All sizes”.

import Definitions.Def_RGMISFast_GoodEvent
import Definitions.Def_RGMISFast_rankLaw
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false

theorem RGMISFast.low_rank_fixed_size_tail {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (u : V) (j k : ℕ) (hk : 1 ≤ k) :
    rankLaw V {r | ∃ A : Finset V, IsRootConnected G u A ∧ A.card = j+1 ∧
      k ≤ (GammaLow G r Δ A).card} ≤
      ENNReal.ofReal ((8*(Δ:ℝ))^j*(1/2:ℝ)^k) := by sorry
