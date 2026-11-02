-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_depolarizing_block_lp
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.depolarizing_block_lp
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:55:37.471745+00:00
-- url     : https://prove2.me/theorems/6aa52807-02e5-4075-bd37-4df0f6f6c0f8
-- title:
--   Example 1 and Appendix A / LP (72): depolarizing finite-blocklength cost
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let $d\ge1$, $0\le p\le1$, $\varepsilon\ge0$, and $n\ge0$. For $k=0,\ldots,n$ put $q_1=d(1-p)+p/d$, $q_2=p/d$, $p_k=q_1^kq_2^{n-k}$, and $w_k=\binom nk(1/d)^k(d-1/d)^{n-k}$. Minimize $d^ns$ over real $s,y_k,r_k$ subject to $y_k-r_k+p_k\ge0$, $y_k\ge0$, $0\le r_k\le s$, $\sum_kw_kr_k=1$, and $\sum_kw_ky_k\le\varepsilon$; denote its infimum by $t$. Then
--
--   $$S_{\rm NS,\varepsilon}^{(1)}(\mathcal D_p^{\otimes n})=\log_2\lceil\sqrt t\rceil.$$
--
--   An optimal solution of the channel SDP exists with $J=\sum_kr_kP_k^n$, $Y=\sum_ky_kP_k^n$, and $V=sI_{d^n}$, attaining the trace objective $d^ns$. Here $P_k^n$ sums all products with exactly $k$ normalized maximally entangled projectors and $n-k$ orthogonal complements. Empty products and $0^0$ equal one, retaining the scalar boundaries.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 18, Example 1 and Appendix A / LP (72): depolarizing finite-blocklength cost

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P65

noncomputable section

open Filter QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakethird100.P65

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (transposeBob)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Independent2.P01 (dampingKraus damping)

open QAlgorithms.Papers.Independent.Gap48.P33 (phaseFlipChannel)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P62 (Stochastic)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized purifiedDistance)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer permute)

open QAlgorithms.Papers.Independent.Information100.P71 (diamond channelPower channelRelative)

open QAlgorithms.Papers.Independent.Support50.P39 (quantumMutualInformation)

variable {A B C D R : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty R]

/-- Example 1 and Appendix A, Eqs.(71)--(72), PDF pp.13,18: finite-blocklength
LP and an attained SDP optimum of the symmetric form. n=0 and d=1 are meaningful
with the usual empty-product and 0^0=1 conventions. -/
theorem depolarizing_block_lp (p e : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (he : 0 ≤ e) (n : ℕ) :
    oneUseSimulationCost .ns (channelPower (basisDepolarizing A p) n) e =
      roundedTraceCost (depolarizingValue (Fintype.card A) n p e) ∧
    ∃ s : ℝ, ∃ y r : Fin (n+1) → ℝ,
      depolarizingFeasible (Fintype.card A) n p e s y r ∧
      traceFeasible (channelPower (basisDepolarizing A p) n) e
        (sectorMatrix A n y) (sectorMatrix A n r) ((s : ℂ) • (1 : Mat (Fin n → A))) ∧
      (Fintype.card A : ℝ)^n * s = traceValue (channelPower (basisDepolarizing A p) n) e := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
