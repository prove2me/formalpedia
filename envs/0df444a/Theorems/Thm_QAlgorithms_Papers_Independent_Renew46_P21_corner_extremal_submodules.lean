-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P21_corner_extremal_submodules
-- name    : QAlgorithms.Papers.Independent.Renew46.P21.corner_extremal_submodules
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:27:27.421994+00:00
-- url     : https://prove2.me/theorems/5b90e296-33b6-4406-a68b-dca40c1cec05
-- title:
--   Extremal submodules annihilated by or generated from an idempotent
-- statement:
--   Let $K$ be a commutative ring with identity, $A$ an associative $K$-algebra that may be nonunital, $e\in A$ an idempotent, and $M$ a right $K$-linear $A$-module. When $A$ has an identity, assume the module is unital. Define
--
--   $$
--   N(M)=\{m\in M:mae=0\text{ for every }a\in A\},\qquad
--   L(M)=\operatorname{span}_K\{(me)a:m\in M,\ a\in A\}.
--   $$
--
--   Both are $A$-submodules. The submodule $N(M)$ is annihilated by $e$ and contains every $A$-submodule annihilated by $e$. The submodule $L(M)$ satisfies $L(M)e=Me$ and is contained in every $A$-submodule $U$ satisfying $Ue=Me$. No simplicity assumption is required. These extremal constructions identify the submodules used by Green's correspondence. Every K-linear A-module homomorphism f:M→P restricts to maps N(M)→N(P) and L(M)→L(P). These restricted maps give the source's action of N and L on morphisms; identities and composition are inherited from restriction of the underlying maps.
-- source:
--   On the irreducible representations of a finite semigroup, arXiv:0712.2076v2, PDF p. 4, Unnumbered N and L paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P21

namespace QAlgorithms.Papers.Independent.Renew46.P21

universe u v w

/-- Unnumbered extremal characterization, p. 4: N is the largest A-submodule
annihilated by e; L is the smallest A-submodule with Le = Me. Both constructions
preserve module homomorphisms by restriction, as required by the source's functor
assertion. No simplicity assumption is present. The two scalar compatibility
hypotheses say A is a K-algebra. -/
theorem corner_extremal_submodules {K : Type u} {A : Type v} {M : Type w}
    [CommRing K] [NonUnitalRing A] [Module K A] [AddCommGroup M] [Module K M]
    (hleft : ∀ (k : K) (a b : A), (k • a) * b = k • (a * b))
    (hright : ∀ (k : K) (a b : A), a * (k • b) = k • (a * b))
    (rho : RightAlgebraAction K A M) (e : A) (he : e * e = e) :
    AlgebraInvariant rho (cornerAnnihilator rho e) ∧
    (∀ m : M, m ∈ cornerAnnihilator rho e ↔ ∀ a : A, rho.act (a * e) m = 0) ∧
    (∀ m ∈ cornerAnnihilator rho e, rho.act e m = 0) ∧
    (∀ U : Submodule K M, AlgebraInvariant rho U →
      (∀ m ∈ U, rho.act e m = 0) → U ≤ cornerAnnihilator rho e) ∧
    AlgebraInvariant rho (cornerGenerated rho e) ∧
    rho.act e '' (cornerGenerated rho e : Set M) = Set.range (rho.act e) ∧
    (∀ U : Submodule K M, AlgebraInvariant rho U →
      rho.act e '' (U : Set M) = Set.range (rho.act e) → cornerGenerated rho e ≤ U) ∧
    (∀ (P : Type w) [AddCommGroup P] [Module K P]
      (sigma : RightAlgebraAction K A P) (f : M →ₗ[K] P),
      (∀ (a : A) (m : M), f (rho.act a m) = sigma.act a (f m)) →
      (∀ m ∈ cornerAnnihilator rho e, f m ∈ cornerAnnihilator sigma e) ∧
      (∀ m ∈ cornerGenerated rho e, f m ∈ cornerGenerated sigma e)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P21
