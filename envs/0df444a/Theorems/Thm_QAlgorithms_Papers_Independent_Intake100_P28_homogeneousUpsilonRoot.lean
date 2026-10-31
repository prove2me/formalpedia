-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P28_homogeneousUpsilonRoot
-- name    : QAlgorithms.Papers.Independent.Intake100.P28.homogeneousUpsilonRoot
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:27:03.923677+00:00
-- url     : https://prove2.me/theorems/f32fcd6c-d3e7-4525-a27f-dc30c8629667
-- title:
--   Remark 1.2: homogeneous root preserves the relevant convexity or concavity
-- statement:
--   Let $n,m$ be positive integers. All matrices are complex and positive semidefinite unless otherwise specified, including singular matrices and zero. For $p,q>0$, put
--   $$
--   \Phi_{p,q}(A_1,\ldots,A_m)=\left(\operatorname{Tr}(\sum_j A_j^p)^{q/p}\right)^{1/q},\quad
--   \Psi_{p,q}(A)=\left(\operatorname{Tr}(\operatorname{Tr}_2 A^p)^{q/p}\right)^{1/q},\quad
--   \Upsilon_{p,q}^{B}(A)=\operatorname{Tr}(B^*A^pB)^{q/p}.
--   $$
--   Here powers are spectral powers, $B$ is an arbitrary fixed complex matrix, and $\operatorname{Tr}_2$ is the unnormalized partial trace over the second factor of $\mathbb C^m\otimes\mathbb C^n$. Convexity and concavity use every mixture weight in $[0,1]$.
--
--   For any fixed $p,q>0$ and $B$, the nonnegative functional $\Upsilon=\Upsilon_{p,q}^{B}$ satisfies
--   $$
--   \Upsilon(tA)=t^q\Upsilon(A)\quad(t\ge0),\qquad
--   \Upsilon\text{ convex (concave)}\ \Longrightarrow\
--   \Upsilon^{1/q}\text{ convex (concave)}.
--   $$
--   Each assertion is on the full positive semidefinite cone. The root implication is conditional on the corresponding property of $\Upsilon$; it does not assume a parameter range in which that property fails.
--
--   This records the homogeneous-root argument used in passing from trace powers to the rooted functionals.
-- source:
--   A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity, arXiv:0710.4167v3, PDF p. 2, Remark 1.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower tr leftMarginal rightMarginal marginalAC)

namespace QAlgorithms.Papers.Independent.Intake100.P28

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Remark 1.2, PDF pp.2,11: homogeneity is retained explicitly. -/
theorem homogeneousUpsilonRoot {n : ℕ} (hn : 0 < n)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (B : Mat (Fin n)) :
    (∀ A ∈ psd (Fin n), ∀ t : ℝ, 0 ≤ t →
      sandwichedTraceFunctional p q B (t • A) = t ^ q * sandwichedTraceFunctional p q B A) ∧
    (ConvexOn ℝ (psd (Fin n)) (sandwichedTraceFunctional p q B) →
      ConvexOn ℝ (psd (Fin n)) (fun A => (sandwichedTraceFunctional p q B A) ^ (1 / q))) ∧
    (ConcaveOn ℝ (psd (Fin n)) (sandwichedTraceFunctional p q B) →
      ConcaveOn ℝ (psd (Fin n)) (fun A => (sandwichedTraceFunctional p q B A) ^ (1 / q))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P28

end
