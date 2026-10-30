-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P39_holevo_eq_radius
-- name    : QAlgorithms.Papers.Independent.Bridge50.P39.holevo_eq_radius
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:48:17.445752+00:00
-- url     : https://prove2.me/theorems/d9598795-d342-44fe-9f0b-5702a414ae2d
-- title:
--   Sandwiched Holevo information equals information radius for every order above one
-- statement:
--   Let $\mathcal N:A\to B$ be any quantum channel between positive, finite-dimensional complex Hilbert spaces, and let $\alpha>1$. All logarithms are base two. For density operators, define
--
--   $$
--   \widetilde D_\alpha(\rho\Vert\sigma)=\frac1{\alpha-1}\log_2\operatorname{Tr}\!\left[\left(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)}\right)^\alpha\right]
--   $$
--
--   when $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$, and set it to $+\infty$ otherwise. Negative powers are generalized inverses on the support. For each finite ensemble of mixed input states $\{p_x,\rho_x\}$ put $\omega_{XB}=\sum_xp_x|x\rangle\langle x|\otimes\mathcal N(\rho_x)$. Then
--
--   $$
--   \widetilde\chi_\alpha(\mathcal N)
--   :=\sup_{\{p_x,\rho_x\}}\inf_{\sigma_B}\widetilde D_\alpha(\omega_{XB}\Vert\omega_X\otimes\sigma_B)
--   =\inf_{\sigma_B}\sup_{\rho_A}\widetilde D_\alpha(\mathcal N(\rho_A)\Vert\sigma_B)
--   =: \widetilde K_\alpha(\mathcal N).
--   $$
--
--   The input $\rho_A$ and comparison $\sigma_B$ range over all density operators on their respective spaces; no comparison state must be strictly positive. This extends the earlier order range $1<\alpha\le2$ to every $\alpha>1$ and identifies the two optimization orders.
-- source:
--   Strong converse exponents for the feedback-assisted classical capacity of entanglement-breaking channels, arXiv:1506.02228v4, PDF p. 9, Lemma 3, (4.6)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P39

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD tensorAction)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P08 (channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Support50.P19
  (channelInformation informationRadius expTwo)

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- PDF p.9, Lemma 3, (4.6): the full alpha>1 extension of WWY14 Lemma 14.
Both optimization orders are kept; no attainment or cardinality reduction is assumed. -/
theorem holevo_eq_radius [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N)
    (a : ℝ) (ha : 1 < a) :
    channelInformation true a N = informationRadius true a N := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P39

end
