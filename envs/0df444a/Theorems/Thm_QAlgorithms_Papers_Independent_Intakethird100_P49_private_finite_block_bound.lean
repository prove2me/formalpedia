-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P49_private_finite_block_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P49.private_finite_block_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:47:43.533051+00:00
-- url     : https://prove2.me/theorems/b5acf76e-99d0-4127-ba7d-5b3414866350
-- title:
--   Supplement V.B, Eq.(183): finite-block private-rate bound, corrected dimension
-- statement:
--   Let $\mathcal E:d\to e$ be CPTP with $d\ge2$, $e\ge1$, and let an actual two-way finite LOCC code use $\mathcal E$ exactly $n>0$ times, from a separable normalized initial state. Its output is within full trace norm $\epsilon\ge0$ of a private target with $k$ key bits and arbitrary finite shields. Let $R=k/n$ and let $D_{\rm out}$ be the total output/target Hilbert-space dimension, including the shields. Let $E$ be a nonnegative real entanglement functional, normalized on all private targets, monotone under dimension-changing LOCC and subadditive on heterogeneous tensors. Assume $g,h\to0$ at zero and the uniform continuity condition $|E(\rho)-E(\sigma)|\le g(\gamma)\log_2D_{\rm out}+h(\gamma)$ whenever $\|\rho-\sigma\|_1\le\gamma$ in its specified error domain. For integer $M\ge2$, require $\gamma=n\delta_{d,M}+\epsilon$ in that domain. Then
--
--   $$R\le M E(\rho_{\mathcal E})+\frac{g(\gamma)\log_2D_{\rm out}+h(\gamma)}n.$$
--
--   The source's reused dimension symbol is corrected to the compared-state dimension. This is a finite-block statement; it imposes no uniform size restriction on private shields and claims no general capacity weak converse. The frozen code's half-norm error is doubled for this full-norm finite-block premise.
-- source:
--   Fundamental limits to quantum channel discrimination, arXiv:1803.02834v4, PDF p. 19, Supplement V.B, Eq.(183): finite-block private-rate bound, corrected dimension

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P49

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Dependency50.P18 (bipartiteTensor)

open QAlgorithms.Papers.Independent.Information100.P71 (diamond AdaptiveTest adaptiveInput adaptiveAccept)

open QAlgorithms.Papers.Independent.Bridge50.P25
  (LOCCOn normalizedChannelChoi TwoWayGenerationCode TwoWayChannelProtocol
   generationCodeError twoWayGenerationCapacity sendChannelRegister StateFunctional
   IsDimensionChangingLOCCMonotone privateStateInPartyOrder)

open QAlgorithms.Papers.Independent.Support50.P07 (amplitudeDampingChannel)

/-- Supplement V.B, PDF p.19, (177)--(183): finite private-generation rate.
The continuity logarithm uses actual total OUTPUT dimension including shields,
correcting the reused printed single-use symbol d. (181) has absolute values:
the target-minus-output direction is essential. No capacity weak converse or
uniform linear shield-size premise is asserted. Independent correction review required. -/
theorem private_finite_block_bound (d e M : ℕ) [NeZero d] [NeZero e]
    (hd : 2 ≤ d) (hM : 2 ≤ M) (E : Superop (Fin d) (Fin e)) (hE : IsChannel E)
    (code : TwoWayGenerationCode E true) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hsecure : 2 * generationCodeError code ≤ epsilon)
    (measure : StateFunctional) (g h : ℝ → ℝ) (domain : Set ℝ)
    (hadmissible : AdmissiblePrivateMeasure measure g h domain)
    (hgamma : code.uses * pbtError d M + epsilon ∈ domain) :
    (code.key : ℝ) / code.uses ≤ M * measure (Fin d) (Fin e) (normalizedChannelChoi E) +
      (g (code.uses*pbtError d M+epsilon) *
        Real.logb 2 (((2^code.key : ℕ)*(code.shield+1))^2) +
       h (code.uses*pbtError d M+epsilon)) / code.uses := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P49

end
