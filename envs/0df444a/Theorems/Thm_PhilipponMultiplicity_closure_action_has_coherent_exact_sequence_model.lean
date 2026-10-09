-- Prove2me | Theorems.Thm_PhilipponMultiplicity_closure_action_has_coherent_exact_sequence_model
-- name    : PhilipponMultiplicity.closure_action_has_coherent_exact_sequence_model
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-09T01:41:59.882501+00:00
-- url     : https://prove2.me/theorems/07160a51-8156-4174-b604-e5fc6513c5fc
-- title:
--   Exact-sequence data with common subobjects for coherent twists
-- statement:
--   Let $X$ be the multiprojective closure of an embedded commutative algebraic group $G$ over a Philippon base field. Let the regular automorphisms $\tau_g$ satisfy the identity and group laws of the coherent-presentation theorem.
--
--   There are abelian groups $L,A$, with $A$ finitely generated, a surjective homomorphism $q:L\to A$, an action $\rho:G(K)\to\operatorname{Aut}(L)$ preserving $\ker q$, and classes $c_i\in L$ indexed by the projective factors.
--
--   There are a set $C$, a permutation action $\sigma:L\to\operatorname{Perm}(C)$, a dimension function $d:C\to\mathbb N$, an Euler-value function $e:C\to\mathbb Q$, and a predicate
--   $$S\subseteq C\times C\times(C\sqcup\{\mathbf 0\}).$$
--   The extra symbol $\mathbf 0$ represents a zero cokernel. Extend $\sigma_l$ to fix it, and set $e(\mathbf 0)=0$. Think of $S(k,a,Q)$ as recording a short exact sequence with subobject $k$, middle object $a$ and cokernel $Q$. The formal requirements on the predicate are
--   $$S(k,a,Q)\ \Longrightarrow\
--   S(\sigma_l k,\sigma_l a,\sigma_l Q),\qquad
--   e(a)=e(k)+e(Q).$$
--
--   For every $l\in L$ and $a\in C$, there are a common subobject $k\in C$ and cokernels $Q,Q'\in C\sqcup\{\mathbf 0\}$ such that
--   $$S(k,a,Q),\qquad S(k,\sigma_l a,Q').$$
--   Every cokernel that belongs to $C$ has dimension strictly less than $d(a)$; the adjoined zero symbol has no dimension condition. For all $l\in\ker q$ and $a\in C$,
--   $$e(\sigma_l a)=e(a).$$
--
--   For every closed subset $V\subseteq X$, there is $a_V\in C$ satisfying
--   $$d(a_V)\le d_V,\qquad d_V=\deg\operatorname{HP}(V),$$
--   where the Hilbert polynomial comes from the actual multigraded coordinate quotient. For every $g\in G(K)$ and every tuple $D_i\ge1$, eventually for natural numbers $n$,
--   $$e\!\left(\sigma_{\,n\rho_{-g}(\sum_i D_ic_i)}a_V\right)
--   =\operatorname{HF}_{\tau_g(V)}(nD).$$
--   The right side is the dimension of the indicated component of the actual ambient homogeneous coordinate quotient. The data are common to all closed subsets; the generator and threshold may vary. Empty subsets and dimension zero are included.
--
--   **Formalization Note.** This is an auxiliary exact-triple model, not a categorical construction of coherent sheaves. Its intended realization uses coherent sheaf classes, line-bundle twists, Euler characteristic, and actual short exact sequences. The predicate records the stated compatibility and common-subobject conditions explicitly. Existence of this realization, its common-subobject construction for all selected objects, the finite class quotient and the exact Hilbert comparison remains Open. In particular, the cited meromorphic-section lemma has additional hypotheses; it motivates the common-subobject input without proving this whole auxiliary model. The parent builds the relation submodule as the span of exact-triple relations and proves all its required properties. Zero cokernels are encoded by the extra symbol so that a dimension-zero object requires no negative-dimensional generator.
--
--   **Verified connected-family reduction (9 October 2026).** An accepted proof-sketch derives kernel Euler invariance from [connected-family local constancy and a kernel-span presentation](https://prove2.me/theorems/f4d5e3e5-02b6-461d-96ed-dd1e33dca448). The invariant twists form an integer submodule; inverse twisting converts equality of family values into invariance under each endpoint difference. This extends to every kernel element. The exact-triple geometry, family realization and coordinate Hilbert comparison remain Open. The original formal statement is unchanged.
-- source:
--   Auxiliary exact-sequence form of the coherent-generator presentation. Stacks Project, Lemma 33.33.2, Euler additivity for short exact sequences, https://stacks.math.columbia.edu/tag/08AA . The common-subobject mechanism is motivated by Lemma 31.25.5, https://stacks.math.columbia.edu/tag/02P2 , and its use in the support-dimension induction of Lemma 33.45.1, https://stacks.math.columbia.edu/tag/0BEL . Lemma 31.25.5 assumes a regular meromorphic section and a coherent sheaf without embedded associated points whose support is the whole scheme; it does not by itself assert the common-source condition for every object in this auxiliary model. The geometric realization, finite class quotient, kernel Euler invariance and exact coordinate Hilbert comparison are explicit Open obligations inherited from the parent. The statement is not a verbatim theorem from these sources.

import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Cardinality
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators Topology
universe u

namespace PhilipponMultiplicity

theorem closure_action_has_coherent_exact_sequence_model
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
          (d : C → ℕ) (e : C → ℚ) (S : C → C → Option C → Prop),
          (∀ l a b Q, S a b Q → S (σ l a) (σ l b) (Q.map (σ l))) ∧
          (∀ a b Q, S a b Q → e b = e a + Q.elim 0 e) ∧
          (∀ l a, ∃ (k : C) (Q Q' : Option C),
            S k a Q ∧ S k (σ (Multiplicative.ofAdd l) a) Q' ∧
            (∀ b ∈ Q, d b < d a) ∧ (∀ b ∈ Q', d b < d a)) ∧
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
