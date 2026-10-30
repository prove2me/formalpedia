-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P05_complementarySmoothedCoherentInformation
-- name    : QAlgorithms.Papers.Independent.Advance50.P05.complementarySmoothedCoherentInformation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:29:14.139352+00:00
-- url     : https://prove2.me/theorems/2c186879-a598-43f0-8e2d-abaeb870096c
-- title:
--   Complementary smoothed coherent information
-- statement:
--   Let $|\Psi\rangle$ be a normalized pure state on positive-dimensional finite systems $A,B,E$, and let $\rho^{AB}$ and $\rho^{AE}$ be its complementary reduced states. For every $\delta>0$, define the subnormalized fidelity ball
--   $$
--   b(r;\delta)=\{s\ge0:\operatorname{Tr}s\le1,\ F(r,s)^2\ge1-\delta^2\}.
--   $$
--   Here $F$ is root fidelity without an added vacuum term. With $\Pi_s$ the support projector and all comparison states normalized, set
--   $$
--   I_{0,\delta}^{A\to B}(\rho^{AB})=\max_{s\in b(\rho^{AB};\delta)}\min_{\sigma_B}-\log_2\operatorname{Tr}[\Pi_s(1_A\otimes\sigma_B)],
--   $$
--   $$
--   I_{2,\delta}^{A\to E}(\rho^{AE})=\min_{t\in b(\rho^{AE};\delta)}\min_{\sigma_E}\log_2\operatorname{Tr}[t^2(1_A\otimes\sigma_E)^{-1}].
--   $$
--   The inverse is the generalized inverse on support, with $+\infty$ for unsupported nonzero $t$ and $-\infty$ for $t=0$. No trace normalization factor is inserted in the order-two expression. Then
--   $$
--   -I_{2,\delta}^{A\to E}(\rho^{AE})\ge I_{0,\delta}^{A\to B}(\rho^{AB}).
--   $$
--   The smoothing and comparison extrema have witnesses. For $\delta\ge1$, the zero smoothing candidate gives $I_{2,\delta}=-\infty$ and $I_{0,\delta}=+\infty$, so the displayed inequality is understood in the extended reals.
--
--   This relates the two complementary smoothed quantities. **Formalization Note:** no environment-dimension lifting equality or duality identity is assumed as a hypothesis; Eq.(72) itself is unchanged.
-- source:
--   Distilling entanglement from arbitrary resources, arXiv:1006.1896v2, PDF p. 21, Lemma 12, Eq.(72): complementary smoothed coherent information

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P05

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P19 (first both epr IsIso)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P35 (elog marginalAB marginalAC)

open QAlgorithms.Papers.Independent.Support50.P21 (dMin weakPositive PositiveTensorBasis)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Buscemi--Datta, arXiv:1006.1896v2, PDF pp.21--22, Lemma 12, (72).
Complementary marginals are computed from the same normalized vector.
All delta>0, including the extended-infinite regime delta>=1. The theorem
uses Eq.(72) unchanged. Eq.(77)'s missing minus sign and Eq.(81)'s H_B/H_E
proof typos are not assumed as identities or repaired by extra hypotheses. -/
theorem complementarySmoothedCoherentInformation
    {A B E : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (psi : EuclideanSpace ℂ (A × (B × E))) (hpsi : ‖psi‖ = 1)
    (delta : ℝ) (hdelta : 0 < delta) :
    -smoothedTwo (marginalAC (pureDensity psi)) delta ≥ smoothedZero (marginalAB (pureDensity psi)) delta ∧
    TwoExtremaAttained (marginalAC (pureDensity psi)) delta ∧
    ZeroExtremaAttained (marginalAB (pureDensity psi)) delta := by sorry

end QAlgorithms.Papers.Independent.Advance50.P05

end
