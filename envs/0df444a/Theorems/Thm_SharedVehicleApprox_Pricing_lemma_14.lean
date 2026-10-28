-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_lemma_14
-- name    : SharedVehicleApprox.Pricing.lemma_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:09.800635+00:00
-- url     : https://prove2.me/theorems/558136af-6118-4f16-a5db-5ed8961abd6d
-- title:
--   Lemma 14, p. 17 — maximum availability in the m-unit system: A_m(q) = r_max·G_{m−1}/G_m ≥ m/(m+n−1)
-- statement:
--   Let $n\ge1$, $m\ge1$ and let $r\in\mathbb R^n$ be a vector of traffic intensities, $r_j\ge0$ with some $r_j>0$. Write $G_m=\sum_{x\in S_{n,m}}\prod_jr_j^{x_j}$, $r_{\max}=\max_jr_j$, and let $\pi$ be the product-form law (4), $\pi(x)=G_m^{-1}\prod_jr_j^{x_j}$ on $S_{n,m}$. Then the maximal availability $A_m=\max_iA_{i,m}$ under $\pi$ satisfies
--   $$A_m=r_{\max}\,\frac{G_{m-1}}{G_m}\ \ge\ \frac{m}{m+n-1}.$$
--
--   This is the pullback step of the framework: by Lemma 12, $A_m$ is the ratio of the $m$-unit to the infinite-unit objective, so the bound transfers infinite-unit guarantees to the $m$-unit system.
--
--   Differences from the source:
--   - generalization: "for any state-independent pricing policy q", with r = r(q) = w(q)/µ(q) → any r with r_j ≥ 0 for all j and r_j > 0 for some j; reason: every traffic intensity vector r(q) (w an invariant distribution, µ_i > 0) is nonnegative with a positive entry, so the statement specializes to r(q)
--   - encoding: A_m(q), the maximum availability of the m-unit system under q → max_i of the availabilities under productForm (r_j^y) m, the law (4); reason: by Theorem 2 the stationary law of q is (4) with r = r(q); the ratio is stated with m ≥ 1 since G_{m−1} needs it
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 17 (PDF 18), Lemma 14; proof pp. 17–18 (PDF 18–19)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

open Finset QueueingFundamentals.Networks Filter Topology

namespace SharedVehicleApprox.Pricing

/-- Lemma 14, p. 17: for `m ≥ 1` and every nonnegative vector `r` of traffic intensities with
some positive entry, the maximal availability under the product-form law (4) is
`A_m = r_max · G_{m−1} / G_m`, and it is at least `m / (m + n − 1)`. -/
theorem lemma_14 {n m : ℕ} [NeZero n] (hm : 1 ≤ m) (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hpos : ∃ j, 0 < r j) :
    univ.sup' univ_nonempty (fun i => availability m (productForm (fun j y => r j ^ y) m) i) =
        rmax r * G r (m - 1) / G r m ∧
      (m : ℝ) / ((m : ℝ) + n - 1) ≤ rmax r * G r (m - 1) / G r m := by sorry

end SharedVehicleApprox.Pricing
