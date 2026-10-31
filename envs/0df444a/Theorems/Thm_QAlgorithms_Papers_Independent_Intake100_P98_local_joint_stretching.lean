-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P98_local_joint_stretching
-- name    : QAlgorithms.Papers.Independent.Intake100.P98.local_joint_stretching
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:08:39.52377+00:00
-- url     : https://prove2.me/theorems/7cb63bac-27db-4119-a532-a7a3b26023eb
-- title:
--   Corollary 4.4: local joint stretching polynomial
-- statement:
--   Let $k\ge1$, and let $\Upsilon$ be the real cone of weakly decreasing nonnegative triples $(\lambda,\mu,\nu)\in\mathbb R^{3k}$ with $|\lambda|+|\mu|=|\nu|$ and $\lambda_i,\mu_i\le\nu_i$. Interpret the proof’s genericity as lying in the size-hyperplane interior of a single chamber of the constructed $\mathrm{LR}_k$, or in the open exterior of its closed hive support. This is conical genericity, and is not identified with affine Steinberg genericity.
--
--   For every such point $x\in\Upsilon$ there are a real $\varepsilon>0$ and a rational polynomial $q(y,t)$ in the $3k$ real triple coordinates $y=(\lambda',\mu',\nu')$ and the dilation variable $t$ such that
--
--   $$
--   q(y,t)=c^{t\nu'}_{t\lambda'\,t\mu'}
--   \quad\text{if }y\in\Upsilon,\ \|y-x\|<\varepsilon,\ t\in\mathbb N,\ t\ge1,\ ty\in\mathbb Z^{3k},
--   $$
--   $$
--   \deg_t q\le3{k-1\choose2},\qquad
--   \deg_{\lambda'}q,\deg_{\mu'}q,\deg_{\nu'}q\le{k-1\choose2}.
--   $$
--
--   The neighborhood is relative to the size hyperplane; the norm is the finite-dimensional coordinate sup norm. Coefficients are evaluated only at integral dilated triples. This retains the advertised local real-neighborhood result, including exterior zero regions. The interpretation of genericity and positive dilation follows the proof and requires independent moderation.
-- source:
--   A polynomiality property for Littlewood-Richardson coefficients, arXiv:math/0308101v2, PDF p. 11, Corollary 4.4: local joint stretching polynomial

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P98

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P98

open QAlgorithms.Papers.Independent.Frontier30.P19

attribute [local instance] Classical.propDecidable

/-- Corollary 4.4, PDF p.11, read by its own proof. Printed: "generic" after
p.9 defined affine SA genericity. Changed: LR conical genericity, the condition
that gives one chamber neighborhood in this proof; the exterior zero region
is retained. Upsilon is a REAL dominant cone; coefficients are evaluated only
when t*y is integral. t>=1 agrees with the positive stretching convention on
p.2. Degrees are total degrees within each block. This interpretation requires
independent moderation and does not identify SA-generic with LR-generic. -/
theorem local_joint_stretching (k : ℕ) (hk : 0 < k)
    (x : Coordinates k → ℝ) (hx : RealDomain x) (hgeneric : LRGeneric x) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ p : MvPolynomial (JointCoordinates k) ℚ,
        JointDegreeAtMost p (Nat.choose (k-1) 2) ∧
        ∀ y : Coordinates k → ℝ, RealDomain y → dist y x < epsilon →
          ∀ t : ℕ, 0 < t → ∀ z : Coordinates k → ℕ,
            (∀ v, (z v : ℝ) = (t : ℝ) * y v) →
            evalReal p (fun v => match v with
              | none => (t : ℝ)
              | some w => y w) = (paddedLRCoefficient z : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P98

end
