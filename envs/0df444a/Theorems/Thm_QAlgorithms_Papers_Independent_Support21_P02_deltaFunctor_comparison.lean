-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P02_deltaFunctor_comparison
-- name    : QAlgorithms.Papers.Independent.Support21.P02.deltaFunctor_comparison
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:27:24.432376+00:00
-- url     : https://prove2.me/theorems/5ae3b703-0848-49ae-8ea2-1d6805596b88
-- title:
--   Theorem VI.2: delta-functor comparison principle
-- statement:
--   Let $\mathcal C$ be an arbitrary category equipped with a distinguished class of composable pairs, called short exact sequences. A cohomological $\delta$-functor means functors $H^n:\mathcal C\to\mathrm{Ab}$, for $n\ge0$, with natural connecting homomorphisms giving long exact sequences. There is no assumed additive structure on $\mathcal C$, and $H^0$ need not be left exact. Let $H$ and $K$ be two such functors. Suppose there are endofunctors $I,U$ and natural transformations $\iota:\mathrm{Id}\Rightarrow I$, $\zeta:I\Rightarrow U$ such that $A\to I(A)\to U(A)$ is distinguished for every $A$.
--
--   1. Let $m\ge0$ and $\alpha:H^0\Rightarrow K^0$. If $H^j(I(A))=0$ for every $A$ and $1\le j\le m$, there is a unique family of natural transformations $\varphi^j:H^j\Rightarrow K^j$ in degrees $0\le j\le m$ with $\varphi^0=\alpha$ and
--   $$
--   \varphi_A^{j+1}\delta_{H,A}^j=\delta_{K,A}^j\varphi_{U(A)}^j\qquad(0\le j<m).
--   $$
--   Here $\delta_{H,A}^j$ is the connecting map of $A\to I(A)\to U(A)$. If both $H^j(I(A))$ and $K^j(I(A))$ vanish for every $A$ and every $j\ge0$, there is a unique such family in all degrees, and all its components are natural isomorphisms if and only if $\alpha$ is a natural isomorphism. The latter hypothesis retains the source's vanishing requirement in degree zero.
--
--   2. Suppose additionally that every distinguished $A\xrightarrow f B\xrightarrow g C$ admits an object $Q$, a map $q:I(B)\to Q$, and maps $\beta:U(A)\to Q$, $\gamma:C\to Q$, such that $A\xrightarrow{\iota_Bf}I(B)\xrightarrow q Q$ is distinguished and
--   $$
--   \beta\zeta_A=qI(f),\qquad \gamma g=q\iota_B.
--   $$
--   The other square is naturality of $\iota$. Then the finite family in part 1 also commutes with the connecting maps of every distinguished sequence for $0\le j<m$. In particular, if $H^j(I(A))=0$ for every $A$ and $j\ge1$, every $\alpha$ extends uniquely to a morphism of $\delta$-functors in every nonnegative degree.
--
--   This comparison principle supplies natural transformations without requiring an abelian source category or injective objects.
--
--   **Formalization Note** The induction on PDF p. 26 pins the finite range and repairs the printed indices in part 2. No uniqueness in degrees greater than $m$ is claimed.
-- source:
--   A Cocycle Model for Topological and Lie Group Cohomology, arXiv:1110.3304v3, PDF p. 25, Theorem VI.2: delta-functor comparison principle

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P02

universe u v w

namespace QAlgorithms.Papers.Independent.Support21.P02

open CategoryTheory

/-- Theorem VI.2, PDF pp. 25--26 (both parts, including the all-degree
corollaries). The proof's induction forces the finite range 0 <= n <= m;
no uniqueness beyond m is asserted. Printed `short sequence` is read as
`short exact sequence`, and the ill-typed `0 <= m < m` and `phi_A^k`
are transcribed as `0 <= n < m` and `phi_A^(n+1)`, as the proof requires.
The printed stronger vanishing assumption n >= 0 in the isomorphism
subclaim is retained, even though the other assertions only require
positive-degree acyclicity. F is omitted because it is unused.
The source category is arbitrary, independently of the topological
conventions of other sections, and H^0 need not be left exact. -/
theorem deltaFunctor_comparison
    {C : Type u} [Category.{v} C] (S : SequenceClass C)
    (R : FunctorialResolution S) (H K : DeltaFunctor.{u, v, w} S) :
    (∀ (m : ℕ) (alpha : H.degree 0 ⟶ K.degree 0),
      (∀ (A : C) (n : ℕ), 1 ≤ n → n ≤ m →
        Limits.IsZero ((H.degree n).obj (R.I.obj A))) →
      ∃ phi : FiniteFamily H K m,
        FiniteResolutionExtension R alpha phi ∧
        (∀ psi : FiniteFamily H K m,
          FiniteResolutionExtension R alpha psi → psi = phi) ∧
        (CompatibleQuotients R → FiniteConnectingCompatibility phi)) ∧
    (∀ (alpha : H.degree 0 ⟶ K.degree 0),
      (∀ (A : C) (n : ℕ),
        Limits.IsZero ((H.degree n).obj (R.I.obj A)) ∧
        Limits.IsZero ((K.degree n).obj (R.I.obj A))) →
      ∃ phi : DegreeFamily H K,
        ResolutionExtension R alpha phi ∧
        (∀ psi : DegreeFamily H K,
          ResolutionExtension R alpha psi → psi = phi) ∧
        ((∀ n, IsIso (phi.component n)) ↔ IsIso alpha)) ∧
    (CompatibleQuotients R →
      (∀ (A : C) (n : ℕ), 1 ≤ n →
        Limits.IsZero ((H.degree n).obj (R.I.obj A))) →
      ∀ alpha : H.degree 0 ⟶ K.degree 0,
        ∃! phi : DeltaMorphism H K, phi.component 0 = alpha) := by sorry

end QAlgorithms.Papers.Independent.Support21.P02
