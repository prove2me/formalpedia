-- Prove2me | Theorems.Thm_PhilipponMultiplicity_closure_action_has_coherent_generator_presentation
-- name    : PhilipponMultiplicity.closure_action_has_coherent_generator_presentation
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-09T01:24:22.850989+00:00
-- url     : https://prove2.me/theorems/3ff78646-e638-4145-a9fb-f6c0fad29ec0
-- title:
--   Coherent generators and relations for translated Hilbert functions
-- statement:
--   Let $X$ be the multiprojective closure of an embedded commutative algebraic group $G$ over a Philippon base field. Let the regular automorphisms $\tau_g$ satisfy $\tau_0=1$ and $\tau_{g+h}=\tau_g\circ\tau_h$.
--
--   There are abelian groups $L,A$, with $A$ finitely generated, a surjective homomorphism $q:L\to A$, an action $\rho:G(K)\to\operatorname{Aut}(L)$, and classes $c_i\in L$ indexed by the projective factors. Every $\rho_g$ preserves $\ker q$.
--
--   There are also a set $C$ of generators, an action $\sigma:L\to\operatorname{Perm}(C)$, a function $d:C\to\mathbb N$, a submodule of relations and an Euler-value function
--   $$R\subseteq\mathbb Z^{(C)},\qquad e:C\to\mathbb Q.$$
--   Write $[a]$ for the standard basis vector at $a$, and extend both the permutation action and $e$ linearly to the free abelian group. The following conditions hold. The submodule $R$ is invariant under the action, and the linear extension of $e$ vanishes on $R$. For every $l\in L$ and $a\in C$ there is a finite integer combination $w$ satisfying
--   $$[\sigma_l a]-[a]-w\in R,\qquad
--   b\in\operatorname{supp}(w)\ \Longrightarrow\ d(b)<d(a).$$
--   For every $l\in\ker q$ and $a\in C$,
--   $$e(\sigma_l a)=e(a).$$
--
--   Finally, for every closed subset $V\subseteq X$, there is $a_V\in C$ with
--   $$d(a_V)\le d_V,\qquad d_V=\deg\operatorname{HP}(V),$$
--   where the Hilbert polynomial is that of the actual multigraded coordinate quotient. For every $g\in G(K)$ and every tuple $D_i\ge1$, eventually for natural numbers $n$,
--   $$e\!\left(\sigma_{\,n\rho_{-g}(\sum_i D_ic_i)}a_V\right)
--   =\operatorname{HF}_{\tau_g(V)}(nD).$$
--   The Hilbert function on the right is the dimension of the indicated component of the actual ambient homogeneous coordinate quotient. The presentation is common to all $V$; the generator and threshold may vary. Empty subsets and dimension zero are included.
--
--   **Formalization Note.** This is an auxiliary geometric presentation problem. The intended model takes $L=\operatorname{Pic}(X)$, $A=\operatorname{NS}(X)$, generators given by isomorphism classes of coherent sheaves, relations from short exact sequences, $d$ given by support dimension (zero for the zero sheaf), and $e$ by Euler characteristic. The support relation is a finite relation involving lower-dimensional generators, including the zero-dimensional case where $w=0$. Existence of this geometric model, finite generation of the class quotient, the support relation and the exact coordinate Hilbert comparison remain Open. The parent constructs the quotient group, its twist action, Euler homomorphism and generated support levels; these structures are not supplied as data here. No freeness or torsion-free assumption is imposed on the quotient groups.
--
--   **Verified exact-sequence reduction (9 October 2026).** An accepted proof-sketch constructs the relation submodule from [exact-triple data with common subobjects](https://prove2.me/theorems/07160a51-8156-4174-b604-e5fc6513c5fc). It extends twist compatibility and Euler additivity from individual triples to their entire relation span. Subtracting two triples with the same subobject produces the required lower-support relation, including zero cokernels and dimension zero. The geometric exact-triple model and its coordinate Hilbert comparison remain Open. The original formal statement is unchanged.
-- source:
--   Auxiliary generator-and-relation formulation of coherent Euler theory. Stacks Project, Lemma 33.33.2 (Euler additivity), https://stacks.math.columbia.edu/tag/08AA ; Lemma 33.45.1 (support-dimension induction using lower-dimensional cokernels), https://stacks.math.columbia.edu/tag/0BEL ; Lemma 36.32.2 (Euler invariance in proper flat families), https://stacks.math.columbia.edu/tag/0B9T ; Lemma 30.17.1 (eventual ample-twist vanishing), https://stacks.math.columbia.edu/tag/01XO . The finite class quotient is motivated by Cheng, Ji, Larson, Olander, Theorem of the Base, Theorem 7.4, pp.18–19, https://mattlarson2399.github.io/Papers/theorem-of-the-base.pdf . These sources motivate the geometric presentation; none asserts this exact repository point-model statement verbatim. All geometric realization and coordinate-comparison obligations remain explicit.

import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Cardinality
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators Topology
universe u

namespace PhilipponMultiplicity

theorem closure_action_has_coherent_generator_presentation
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val)) :
    ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module ℤ L)
      (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∃ (ρ : Multiplicative G.Point →* (L ≃ₗ[ℤ] L)) (c : G.FactorIndex → L),
        (∀ g x, q x = 0 → q (ρ g x) = 0) ∧
        ∃ (C : Type u) (σ : Multiplicative L →* Equiv.Perm C)
          (d : C → ℕ) (R : Submodule ℤ (C →₀ ℤ)) (e : C → ℚ),
          (∀ l v, v ∈ R → Finsupp.lmapDomain ℤ ℤ (σ l) v ∈ R) ∧
          (∀ v ∈ R, Finsupp.linearCombination ℤ e v = 0) ∧
          (∀ l a, ∃ w : C →₀ ℤ,
            (∀ b ∈ w.support, d b < d a) ∧
            Finsupp.single (σ (Multiplicative.ofAdd l) a) 1 -
              Finsupp.single a 1 - w ∈ R) ∧
          (∀ l, q l = 0 → ∀ a, e (σ (Multiplicative.ofAdd l) a) = e a) ∧
          ∀ (V : Set (groupProjectiveClosure G)),
            @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
            ∃ a : C,
              d a ≤ SectionThree.locusDimension G.ambient (Subtype.val '' V) ∧
              ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
                ∃ N : ℕ, ∀ n ≥ N,
                  e (σ (Multiplicative.ofAdd
                    (n • ρ (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i))) a) =
                    (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
                      (G.ambient.vanishingIdeal (Subtype.val '' (τ g '' V)))
                      (fun i => D i * n) : ℚ) := by sorry

end PhilipponMultiplicity
