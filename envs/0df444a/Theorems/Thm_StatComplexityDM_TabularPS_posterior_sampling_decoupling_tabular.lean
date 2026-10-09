-- Prove2me | Theorems.Thm_StatComplexityDM_TabularPS_posterior_sampling_decoupling_tabular
-- name    : StatComplexityDM.TabularPS.posterior_sampling_decoupling_tabular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:18.591823+00:00
-- url     : https://prove2.me/theorems/acdca977-6a5e-4365-8309-90c88c4fe0ee
-- title:
--   Proof of Proposition 5.4 — posterior-sampling decoupling bound
-- statement:
--   Let $\mu$ be a finitely supported prior on normalized tabular MDPs. Draw $M$ and an independent $M'$ from $\mu$, and use the optimal policy $\pi_{M'}$ as the posterior-sampling policy. For a normalized reference model $\bar M$ and every $\eta>0$,
--   $$
--   \mathbb E_{M\sim\mu}[f^M(\pi_M)-f^{\bar M}(\pi_M)]
--   \le\frac{HSA}{2\eta}+\eta\,
--      \mathbb E_{M,M'\sim\mu}\mathbb E^{\bar M,\pi_{M'}}
--      \left[\sum_{h=1}^{H}D_{TV}^2(P_h^M,P_h^{\bar M})
--                   +D_{TV}^2(R_h^M,R_h^{\bar M})\right].
--   $$
--   The bound decouples the model that determines the policy from the model whose kernels are compared.
--
--   **Formalization Note** The two sums over the prior are independent draws. Finite alphabets and zero-based layer indices represent the paper's tabular setting. Reward normalization includes both §5.2 conditions: individual rewards and almost-sure total reward lie in $[0,1]$.
-- source:
--   arXiv:2112.13487v3, §5.2.1, proof of Proposition 5.4, pp. 34–35, unnumbered final display on p. 35

import Mathlib
import Definitions.Def_StatComplexityDM_TabularPS_MDP

namespace StatComplexityDM.TabularPS

/-- The unnumbered decoupling inequality on pp. 34–35. -/
theorem posterior_sampling_decoupling_tabular {S A W I : Type*}
    [Fintype S] [Fintype A] [Fintype W] [Fintype I]
    [Nonempty S] [Nonempty A] [Nonempty W]
    (H : ℕ) (hH : 1 ≤ H) (d1 : S → ℝ) (rv : W → ℝ)
    (Ms : I → TabMDP S A W H) (w : I → ℝ)
    (Mbar : TabMDP S A W H)
    (piStar : TabMDP S A W H → Policy S A H) (η : ℝ)
    (hd1 : StatComplexityDM.LowerBound.IsDist d1) (hw : StatComplexityDM.LowerBound.IsDist w)
    (hMs : ∀ i, IsTabMDP (Ms i) ∧ RewardsNormalized d1 rv (Ms i))
    (hMbar : IsTabMDP Mbar ∧ RewardsNormalized d1 rv Mbar)
    (hpiStar : ∀ M, IsTabMDP M → RewardsNormalized d1 rv M →
      IsPolicy (piStar M) ∧
        ∀ π, IsPolicy π → value d1 rv M π ≤ value d1 rv M (piStar M))
    (hη : 0 < η) :
    ∑ i, w i * (value d1 rv (Ms i) (piStar (Ms i)) -
      value d1 rv Mbar (piStar (Ms i))) ≤
      ((H : ℝ) * Fintype.card S * Fintype.card A) / (2 * η) +
        η * ∑ i, w i * ∑ j, w j *
          expectedLocalTVSq d1 (Ms i) Mbar (piStar (Ms j)) := by sorry

end StatComplexityDM.TabularPS
