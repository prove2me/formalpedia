-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_populationMoments
-- name    : QAlgorithms.Papers.Independent.Information100.P37.populationMoments
-- status  : Disproved
-- author  : @Goku
-- created : 2026-10-19T11:03:15.678577+00:00
-- url     : https://prove2.me/theorems/b081be3e-c8d3-473c-8e44-c7d05740cf24
-- title:
--   §II.B, Eqs. (5)–(7): centered simplex covariance
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   For all basis indices $i,j$, writing $\delta_{ij}$ for the Kronecker delta and $x=p-\mathbf1/d$,
--   $$\mathbb E p_i=\frac1d,\qquad \mathbb E[p_ip_j]=\frac{1+\delta_{ij}}{d(d+1)},\qquad \mathbb E[xx^T]=\frac{H_d}{d(d+1)}.$$
--   Every simplex population has $\mathbf1^Tx=0$.
--
--   The covariance is isotropic on the entire zero-sum subspace and vanishes at $d=1$.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 2, §II.B, Eqs. (5)–(7): centered simplex covariance

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.2, (5)--(7): scalar moments and isotropic centered covariance. -/
theorem populationMoments [Nonempty ι] :
    let d := (Fintype.card ι : ℝ)
    (∀ i : ι, (∫ p, p i ∂simplexLaw ι) = 1 / d) ∧
    (∀ i j : ι, (∫ p, p i * p j ∂simplexLaw ι) =
      (1 + if i = j then 1 else 0) / (d * (d + 1))) ∧
    (∀ p : ι → ℝ, IsPopulation p → ∑ i, centered p i = 0) ∧
    (∀ i j : ι, (∫ p, centered p i * centered p j ∂simplexLaw ι) =
      zeroSumProjector ι i j / (d * (d + 1))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
