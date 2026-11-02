-- Prove2me | Theorems.Thm_SpikedWishart_Separated_null_wishart_top_eigenvalue_edge_rate
-- name    : SpikedWishart.Separated.null_wishart_top_eigenvalue_edge_rate
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-02T02:40:34.286817+00:00
-- url     : https://prove2.me/theorems/3a07c274-287a-4268-af08-9560dfe713d2
-- title:
--   Upper edge of the null complex Wishart matrix with polynomial rate: $M^l\,P(\lambda_1(S) > (1+\sqrt{N/M})^2+\varepsilon) \to 0$
-- statement:
--   Let $X$ be an $M\times N$ array of i.i.d. standard complex Gaussian entries (the law `SpikedWishart.SoftEdge.sampleLaw M N`), so that its rows $\vec y_1,\dots,\vec y_M\in\mathbb C^N$ are independent with covariance $I_N$, and let $\lambda_1$ be the largest eigenvalue of the null sample covariance matrix $S=\frac1M\sum_{j=1}^M \vec y_j\vec y_j^{\,*}$ (`largestEig M 1 (fun _ => 1) X`). For every $\varepsilon>0$, every power $l\in\mathbb N$ and all sequences $M_n\to\infty$, $N_n\le M_n$,
--
--   $$M_n^{\,l}\;\mathbb P\Big(\lambda_1(S_n) > \big(1+\sqrt{N_n/M_n}\big)^2+\varepsilon\Big)\longrightarrow 0 .$$
--
--   Role: the edge bound localises the largest eigenvalue of the null block in the parent ($l=0$), and the polynomial rate controls the truncation error of the resolvent moments (Q2 children, $l=3$).
--
--   **Formalization Note**: the ratio $N_n/M_n$ is not assumed to converge; $N_n=0$ is allowed (then `largestEig` is the empty supremum $0$ and the event is empty). For Gaussian entries the probability is in fact $O(M e^{-cM})$ by the concentration bound of Davidson-Szarek.
-- source:
--   Z. D. Bai and J. W. Silverstein, Spectral Analysis of Large Dimensional Random Matrices, 2nd ed., Springer 2010, https://doi.org/10.1007/978-1-4419-0661-8, Theorem 5.9 ($P(\lambda_{\max}\ge(1+\sqrt y)^2+x)=o(n^{-l})$); Gaussian case: K. R. Davidson and S. J. Szarek, Local operator theory, random matrices and Banach spaces, Handbook of the Geometry of Banach Spaces I (2001), https://doi.org/10.1016/S1874-5849(01)80010-3, Theorem II.13

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Model
import Definitions.Def_SpikedWishart_Separated_GUE
open Filter Topology MeasureTheory Matrix
open scoped ComplexOrder

namespace SpikedWishart.Separated

theorem null_wishart_top_eigenvalue_edge_rate :
  ∀ (ε : ℝ), 0 < ε → ∀ (l : ℕ) (M N : ℕ → ℕ), Tendsto M atTop atTop → (∀ n, N n ≤ M n) →
    Tendsto (fun n => (M n : ℝ) ^ l * (SpikedWishart.SoftEdge.sampleLaw (M n) (N n)).real
        {X | (1 + Real.sqrt ((N n : ℝ) / M n)) ^ 2 + ε < largestEig (M n) 1 (fun _ => 1) X})
      atTop (𝓝 0) := by sorry

end SpikedWishart.Separated
