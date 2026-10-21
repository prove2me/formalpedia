-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P15_proposition_I_2_3
-- name    : QAlgorithms.Papers.Independent.Next46.P15.proposition_I_2_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:15:30.19099+00:00
-- url     : https://prove2.me/theorems/5278b2cf-7567-4596-a13a-8ef918310b5f
-- title:
--   Fundamental results of locally convex differential calculus
-- statement:
--   Let $E,F$ be Hausdorff real locally convex spaces, $U\subseteq E$ open, and $f:U\to F$ continuously differentiable in the Michal–Bastiani sense. Then:
--
--   1. Each $df(x):E\to F$ is continuous and real linear.
--   2. Whenever $x+[0,1]h\subseteq U$, the represented weak integral exists and
--   $$f(x+h)-f(x)=\int_0^1 df(x+th)h\,dt.$$
--   Moreover, $f$ is locally constant exactly when all its directional derivatives vanish.
--   3. The map $f$ is continuous.
--   4. If $f$ is $C^n$ with $n\ge2$, then $d^nf(x)$ is symmetric and $n$-linear for every $x\in U$.
--   5. If $n\ge1$, $f$ is $C^n$, and the segment lies in $U$, the Taylor remainder is represented in $F$ and
--   $$f(x+h)=\sum_{j=0}^{n-1}\frac{d^jf(x)(h,\ldots,h)}{j!}+\frac1{(n-1)!}\int_0^1(1-t)^{n-1}d^nf(x+th)(h,\ldots,h)\,dt.$$
--   Here $d^0f(x)=f(x)$.
--   6. For a Hausdorff locally convex space $Z$, open $V\subseteq F$, and $C^1$ maps $f_1:U\to V$, $f_2:V\to Z$, the composite is $C^1$ and
--   $$d(f_2\circ f_1)(x)h=df_2(f_1(x))(df_1(x)h).$$
--   Composition also preserves $C^k$ for every positive finite $k$, and preserves smoothness.
--
--   These statements provide calculus without normability or completeness assumptions. Complex models are viewed as real spaces for these real derivatives. A weak integral means a vector representing all scalar integrals against continuous real linear functionals.
-- source:
--   Towards a Lie theory for locally convex groups, arXiv:1501.06269v1, PDF p. 12, Proposition I.2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P15

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P15

open Set Filter Topology

open scoped BigOperators

universe u v w z

/-- Proposition I.2.3, PDF pp.12--13, all six clauses. Taylor order n is
positive, its finite sum has j=0,...,n-1, and its remainder coefficient is
1/(n-1)!. Weak-integral existence is asserted without completeness. -/
theorem proposition_I_2_3
    {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E]
    {F : Type v} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [LocallyConvexSpace ℝ F] [T2Space F]
    {Z : Type w} [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z]
    [LocallyConvexSpace ℝ Z] [T2Space Z]
    (U : Set E) (hU : IsOpen U) (f : E → F) (hf : IsMBC1On U f) :
    (∀ x ∈ U, ∃ A : E →L[ℝ] F, ∀ h : E, directionalDerivative f x h = A h) ∧
    ((∀ x h : E, (∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • h ∈ U) →
        RepresentsWeakIntegral (fun t => directionalDerivative f (x + t • h) h)
          (f (x + h) - f x)) ∧
      (IsLocallyConstant (fun x : U => f x.val) ↔
        ∀ x ∈ U, ∀ h : E, directionalDerivative f x h = 0)) ∧
    ContinuousOn f U ∧
    (∀ n : ℕ, 2 ≤ n → IsMBCFiniteOn U f n → ∀ x ∈ U,
      ∃ A : MultilinearMap ℝ (fun _ : Fin n => E) F,
        (∀ h : Fin n → E, iteratedDirectional f n x h = A h) ∧
        (∀ (s : Equiv.Perm (Fin n)) (h : Fin n → E), A (h ∘ s) = A h)) ∧
    (∀ n : ℕ, 1 ≤ n → IsMBCFiniteOn U f n → ∀ x h : E,
      (∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • h ∈ U) →
      ∃ remainder : F,
        RepresentsWeakIntegral
          (fun t => ((1 - t) ^ (n - 1)) •
            iteratedDirectional f n (x + t • h) (fun _ => h)) remainder ∧
        f (x + h) =
          (∑ j ∈ Finset.range n, ((Nat.factorial j : ℝ)⁻¹) •
            iteratedDirectional f j x (fun _ => h)) +
          ((Nat.factorial (n - 1) : ℝ)⁻¹) • remainder) ∧
    (∀ (V : Set F), IsOpen V → ∀ (f1 : E → F) (f2 : F → Z),
      Set.MapsTo f1 U V →
      ((IsMBCFiniteOn U f1 1 → IsMBCFiniteOn V f2 1 →
        IsMBCFiniteOn U (f2 ∘ f1) 1 ∧
        ∀ x ∈ U, ∀ h : E,
          directionalDerivative (f2 ∘ f1) x h =
            directionalDerivative f2 (f1 x) (directionalDerivative f1 x h)) ∧
      (∀ k : ℕ, 1 ≤ k → IsMBCFiniteOn U f1 k → IsMBCFiniteOn V f2 k →
        IsMBCFiniteOn U (f2 ∘ f1) k) ∧
      (IsMBSmoothOn U f1 → IsMBSmoothOn V f2 → IsMBSmoothOn U (f2 ∘ f1)))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P15

end
