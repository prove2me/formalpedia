-- Prove2me | Theorems.Thm_WRay_forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial
-- name    : WRay.forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/44831302-395a-5441-ac92-140208a5f825
-- title:
--   Unit-Kummer witnesses for q-torsion Hopf points over inertia-fixed base
-- statement:
--   Fix an odd prime $q$ and a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $q$, in the sense that $q$ is a non-unit of $A$; write $I$ for the inertia subgroup of $A$ over $\mathbb{Q}$, viewed inside $\Gamma_{\mathbb{Q}} = \overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ as the image of the inertia subgroup of the decomposition group under the inclusion of the latter. Let $O$ be a discrete valuation domain in which $q$ is irreducible, equipped with an $O$-algebra structure on $A$ and an injective ring map $\iota : O \to A$ inducing the structure map, such that $\sigma \in I$ if and only if $\sigma$ fixes $\iota(x)$ for every $x \in O$, and every element of $A$ fixed by all of $I$ lies in the range of $\iota$. Let $B$ be a commutative, cocommutative Hopf algebra over $O$ that is finite and free as an $O$-module, and assume that for every commutative $O$-algebra $T$ each element of the convolution monoid `WithConv (B →ₐ[O] T)` of $T$-points satisfies $f^q = 1$. Let $n : \Gamma_{\mathbb{Q}} \to \mathbb{N}$ satisfy $\sigma\zeta = \zeta^{n(\sigma)}$ for all $\zeta$ with $\zeta^q = 1$. Let $D$ be a submonoid of the convolution monoid of $A$-points of $B$ such that: for $\sigma \in I$, $f \in D$ and any point $g$ with $g(b) = \sigma(f(b))$ for all $b \in B$, one has $g = f^{n(\sigma)}$; and for $\sigma \in I$ and any points $f, g$ with $g(b) = \sigma(f(b))$ for all $b$, there is $d \in D$ with $g = f\,d$. The conclusion is that there exist $t \in \mathbb{N}$ and families $u, \beta : \mathrm{Fin}\,t \to \overline{\mathbb{Q}}$ such that each $u_i$ has $A$-valuation $1$, each $u_i$ is fixed by every $\sigma \in I$, $\beta_i^q = u_i$ for all $i$, and every $\sigma \in I$ which acts trivially on the $q$-th roots of unity and fixes every $\beta_i$ satisfies: whenever $f, g$ are $A$-points of $B$ with $g(b) = \sigma(f(b))$ for all $b \in B$, then $g = f$.
--
--   This is a Raynaud-type statement in the case $e = 1$: for a finite flat $q$-torsion commutative group scheme over the inertia-fixed discrete valuation ring $O$ which is an extension governed by the submonoid $D$ (constant quotient by multiplicative-type subgroup), the inertia action on $\overline{\mathbb{Q}}$-points is cut out by finitely many Kummer classes of units $u_i$, so that inertia elements trivial on $\mu_q$ and on the chosen $q$-th roots $\beta_i$ act trivially on all points. It is used by [`WRay.exists_unitKummer_witness_of_mem_V1`](thm.html#WRay.exists_unitKummer_witness_of_mem_V1) in the analysis of ramification at $q$, and is obtained from the block decomposition and block-idempotent results [`KummerO.exists_units_of_block`](thm.html#KummerO.exists_units_of_block) and [`KummerO.exists_blockIdempotents_of_quotient_inertiaTrivial`](thm.html#KummerO.exists_blockIdempotents_of_quotient_inertiaTrivial) together with the counting of points [`HopfAlgebra.natCard_algHom_eq_finrank_of_charZero`](thm.html#HopfAlgebra.natCard_algHom_eq_finrank_of_charZero) and the monoid-algebra presentation [`HopfAlgebra.exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid`](thm.html#HopfAlgebra.exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WRay_forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem WRay.forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hirr : Irreducible (q : O))
    [Algebra O ↥A] (ι : O →+* ↥A) (hι : Function.Injective ι) (hιalg : ∀ x : O, algebraMap O ↥A x = ι x)
    (hιfix : ∀ σ : Γℚ, σ ∈ A.inertiaSubgroupIn ℚ ↔ ∀ x : O, σ ((ι x : ↥A) : AlgebraicClosure ℚ) = ((ι x : ↥A) : AlgebraicClosure ℚ))
    (hιmax : ∀ a : ↥A, (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (a : AlgebraicClosure ℚ) = (a : AlgebraicClosure ℚ)) → a ∈ Set.range ι)
    (B : Type) [CommRing B] [HopfAlgebra O B] [Module.Finite O B] [Module.Free O B] [Coalgebra.IsCocomm O B]
    (hBq : ∀ (T : Type) [CommRing T] [Algebra O T] (f : WithConv (B →ₐ[O] T)), f ^ q = 1)
    (n : Γℚ → ℕ)
    (hn : ∀ σ (ζ : AlgebraicClosure ℚ), ζ ^ q = 1 → σ ζ = ζ ^ n σ)
    (D : Submonoid (WithConv (B →ₐ[O] ↥A)))
    (hDcyc : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ f ∈ D, ∀ g : WithConv (B →ₐ[O] ↥A),
      (∀ b : B, ((WithConv.ofConv g b : ↥A) : AlgebraicClosure ℚ) = σ ((WithConv.ofConv f b : ↥A) : AlgebraicClosure ℚ)) → g = f ^ n σ)
    (hquot : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ f g : WithConv (B →ₐ[O] ↥A),
      (∀ b : B, ((WithConv.ofConv g b : ↥A) : AlgebraicClosure ℚ) = σ ((WithConv.ofConv f b : ↥A) : AlgebraicClosure ℚ)) → ∃ d ∈ D, g = f * d) :
    ∃ (t : ℕ) (u β : Fin t → AlgebraicClosure ℚ),
      (∀ i, A.valuation (u i) = 1) ∧
      (∀ i, ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (u i) = u i) ∧
      (∀ i, (β i) ^ q = u i) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ,
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ) →
        (∀ i, σ (β i) = β i) →
        ∀ f g : WithConv (B →ₐ[O] ↥A),
          (∀ b : B, ((WithConv.ofConv g b : ↥A) : AlgebraicClosure ℚ) = σ ((WithConv.ofConv f b : ↥A) : AlgebraicClosure ℚ)) → g = f) := by sorry
