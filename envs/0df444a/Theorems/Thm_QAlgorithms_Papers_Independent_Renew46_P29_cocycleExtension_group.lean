-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P29_cocycleExtension_group
-- name    : QAlgorithms.Papers.Independent.Renew46.P29.cocycleExtension_group
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:57:16.605991+00:00
-- url     : https://prove2.me/theorems/df414b14-0942-42c0-9089-3fffbf7f6bb4
-- title:
--   The group defined by a normalized two-cocycle
-- statement:
--   Let $G$ be a group, let $A$ be an additive abelian group with an action of $G$ by automorphisms, and let $f:G\times G\to A$ satisfy $f(g,1)=f(1,g)=0$ and
--
--   $$f(g,h)+f(gh,k)=g\cdot f(h,k)+f(g,hk).$$
--
--   There is a group structure on $A\times G$ with multiplication, identity, inverse and conjugation
--
--   $$\begin{aligned}(a,g)(b,h)&=(a+g\cdot b+f(g,h),gh),\\
--   1&=(0,1),\\
--   (a,g)^{-1}&=(-g^{-1}\cdot(a+f(g,g^{-1})),g^{-1}),\\
--   (a,g)(b,h)(a,g)^{-1}&=(a+g\cdot b-(ghg^{-1})\cdot a+f(g,h)-f(ghg^{-1},g),ghg^{-1}).\end{aligned}$$
--
--   The projection $q(a,g)=g$ is a surjective homomorphism. Its kernel is $A\times\{1\}$, identified with $A$ by $a\mapsto(a,1)$, and conjugation satisfies $x(a,1)x^{-1}=(q(x)\cdot a,1)$ for every $x\in A\times G$ and $a\in A$.
--
--   This construction realizes the prescribed action in an algebraic abelian extension.
-- source:
--   Abelian extensions of infinite-dimensional Lie groups, arXiv:math/0402303v1, PDF p. 7, Lemma II.1

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P29

namespace QAlgorithms.Papers.Independent.Renew46.P29

open Set Filter Topology

universe u v

section AlgebraicExtension

variable {G : Type u} [Group G] {A : Type v} [AddCommGroup A]

variable [DistribMulAction G A]

/-- Lemma II.1, PDF pp. 7–8: the multiplication, unit, inverse, full
conjugation formula, quotient homomorphism, kernel identification, and
induced action. The normalized cocycle identity corrects the printed typo
on p. 7. The full conjugation formula (2.3), including +f(g,g'), also
appears in the last proof line on p. 8 and is retained exactly. No topology
is assumed. -/
theorem cocycleExtension_group
    (f : G → G → A) (hf : NormalizedTwoCocycle f) :
    ∃ groupStructure : Group (A × G),
      letI := groupStructure
      (∀ x y : A × G, x * y = extensionMul f x y) ∧
      (1 : A × G) = (0, 1) ∧
      (∀ x : A × G, x⁻¹ = extensionInv f x) ∧
      (∀ (a b : A) (g h : G),
        (a, g) * (b, h) * (a, g)⁻¹ =
          (a + g • b - (g * h * g⁻¹) • a + f g h - f (g * h * g⁻¹) g,
            g * h * g⁻¹)) ∧
      (∃ q : (A × G) →* G,
        (∀ x, q x = x.2) ∧ Function.Surjective q ∧
        (∀ x, x ∈ q.ker ↔ x.2 = 1) ∧
        ∃ i : Multiplicative A ≃* q.ker,
          (∀ a, (i a).val = (Multiplicative.toAdd a, 1)) ∧
          ∀ (x : A × G) (a : A),
            x * (a, 1) * x⁻¹ = (q x • a, 1)) := by sorry

end AlgebraicExtension

end QAlgorithms.Papers.Independent.Renew46.P29
