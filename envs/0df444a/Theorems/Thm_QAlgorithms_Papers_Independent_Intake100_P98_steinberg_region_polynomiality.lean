-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P98_steinberg_region_polynomiality
-- name    : QAlgorithms.Papers.Independent.Intake100.P98.steinberg_region_polynomiality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:07:19.840259+00:00
-- url     : https://prove2.me/theorems/a8392861-8424-41de-a88a-1a5e8376c0a9
-- title:
--   Proposition 3.3: polynomiality in the interiors of Steinberg regions
-- statement:
--   Let $k\ge1$. A partition is a weakly decreasing $k$-tuple of nonnegative integers, padded by zeros. For a triple $x=(\lambda,\mu,\nu)$ assume $|\lambda|+|\mu|=|\nu|$, where $|\lambda|=\sum_i\lambda_i$. Write $c^\nu_{\lambda\mu}$ for the ordinary homogeneous Littlewood–Richardson coefficient.
--
--   Allow real coordinates on the size hyperplane to describe regions. Form the affine Steinberg arrangement with all walls
--
--   $$
--   \bigl\langle\sigma(\lambda+\delta)+\tau(\mu+\delta)-(\nu+2\delta),\theta(\omega_j)\bigr\rangle=0,
--   \qquad\sigma,\tau,\theta\in S_k,\quad1\le j\le k-1,
--   $$
--
--   where $\delta$ is the half-root sum and $\omega_j$ are the fundamental weights. Label the chambers of the Kostant complex once, with label zero outside its support; fix a total order on permutations. For each generic real triple, let $v_{\sigma\tau}$ be the label of its Steinberg argument and let $p_v$ be the associated Kostant polynomial, with $p_0=0$. Define
--
--   $$
--   P(x)=\sum_{\sigma,\tau\in S_k}(-1)^{\operatorname{inv}(\sigma\tau)}
--   p_{v_{\sigma\tau}}\bigl(\sigma(\lambda+\delta)+\tau(\mu+\delta)-(\nu+2\delta)\bigr).
--   $$
--
--   On each open region $R$ of this affine arrangement, relative to the size hyperplane, $P$ is a rational polynomial in the triple coordinates. At every integral partition triple in $R$, $P(x)=c^\nu_{\lambda\mu}$. This separates polynomiality on real region interiors from coefficient evaluation at integral points; walls are excluded.
-- source:
--   A polynomiality property for Littlewood-Richardson coefficients, arXiv:math/0308101v2, PDF p. 9, Proposition 3.3: polynomiality in the interiors of Steinberg regions

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P98

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P98

open QAlgorithms.Papers.Independent.Frontier30.P19

attribute [local instance] Classical.propDecidable

/-- Proposition 3.3, PDF p.9. P is the actual sum (28), and each affine
arrangement region is open relative to the size hyperplane. Polynomial identity
is on all real points of the region; LR identity is on its integral partitions.
The region supplies the size equality; containment is not assumed.
No conclusion on walls or nongeneric points is inserted. -/
theorem steinberg_region_polynomiality (k : ℕ) (hk : 0 < k) :
    ∀ s : WallIndex k → Bool, ∃ p : MvPolynomial (Coordinates k) ℚ,
      (∀ x ∈ steinbergRegion s, steinbergP x = evalReal p x) ∧
      (∀ x : Coordinates k → ℕ, (∀ b : Fin 3, Antitone (fun i => x (b,i))) →
        realTriple x ∈ steinbergRegion s →
          steinbergP (realTriple x) = (paddedLRCoefficient x : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P98

end
