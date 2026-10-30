-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P07_weak_converse
-- name    : QAlgorithms.Papers.Independent.Advance50.P07.weak_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:40:57.96198+00:00
-- url     : https://prove2.me/theorems/3a493974-3fc8-4f0b-9e0d-8f3a39d763d4
-- title:
--   Information-spectrum weak converse
-- statement:
--   Let $R,B$ be nonzero finite-dimensional base registers and let $\rho_n^{R_nB_n}$ be any normalized states on $R_n=R^{\otimes n}$ and $B_n=B^{\otimes n}$ for $n\ge1$. Define $p$, $S_0^P$ and $\widetilde I^c_{0,\delta}$ by (10), (12), (14), with normalized comparison states. Then the one-sided outer limit exists and
--
--   $$\lim_{\delta\downarrow0}\liminf_{n\to\infty}\frac1n\max_{P_n\in p(\rho_n;\delta)}\min_{\sigma_n^{B_n}\in\mathcal S(B_n)}S_0^{P_n}(\rho_n\Vert1_{R_n}\otimes\sigma_n^{B_n})\le\min_{\widehat\sigma^B}\underline D(\widehat\rho^{RB}\Vert\widehat1_R\otimes\widehat\sigma^B).$$
--
--   Here $\underline D$ is the supremum of $\gamma$ for which $\liminf_n\operatorname{Tr}(\rho_n-2^{n\gamma}\sigma_n)_+=1$. All endpoints are extended real; the comparison-sequence minimum and each finite-block effect/comparison optimization are attained. This supplies the arbitrary-channel weak converse. The source proof's eventual bound by a liminf must be replaced by a bound with an arbitrarily small slack; the statement is unchanged.
-- source:
--   The quantum capacity of channels with arbitrarily correlated noise, arXiv:0902.0158v5, PDF p. 13, Lemma 16 (Weak converse)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P07

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Advance50.P07

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD petzD)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative Density elog)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P19 (marginalRA marginalRB)

open QAlgorithms.Papers.Independent.Support50.P21 (PositiveTensorBasis)

/-- Lemma 16, PDF pp.13–14. The spectral-INF minimum is attained by a
single normalized comparison-state sequence. The proof's liminf step on p.14
must use beta-eta, not an eventual lower bound by beta itself. -/
theorem weak_converse {R B : Type} [Fintype R] [Fintype B]
    [DecidableEq R] [DecidableEq B] [Nonempty R] [Nonempty B]
    (rho : (k : ℕ) → Mat (PositiveTensorBasis R k × PositiveTensorBasis B k))
    (hrho : ∀ k, IsDensityMatrix (rho k)) :
    Filter.liminf (smoothRate rho) (𝓝[>] (0 : ℝ)) ≤ infCoherent rho ∧
    Tendsto (smoothRate rho) (𝓝[>] (0 : ℝ))
      (𝓝 (Filter.liminf (smoothRate rho) (𝓝[>] (0 : ℝ)))) ∧
    (∃ sigma : (k : ℕ) → {tau : Mat (PositiveTensorBasis B k) // Density tau}, infCoherent rho = comparisonInf rho sigma) ∧
    (∀ delta : ℝ, 0 ≤ delta → ∀ k : ℕ, OperatorAttained (rho k) delta) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P07

end
