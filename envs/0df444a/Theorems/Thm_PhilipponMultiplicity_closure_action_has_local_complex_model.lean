-- Prove2me | Theorems.Thm_PhilipponMultiplicity_closure_action_has_local_complex_model
-- name    : PhilipponMultiplicity.closure_action_has_local_complex_model
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-10T00:22:46.913427+00:00
-- url     : https://prove2.me/theorems/799c6ab6-409d-4f14-b567-a940d6ef43da
-- title:
--   Local bounded cochain complexes for the coherent Euler model
-- statement:
--   Let $X$ be the multiprojective closure of an embedded commutative algebraic group $G$ over a Philippon base field $K$, with regular translation automorphisms $\tau_g$ satisfying the identity and group laws.
--
--   There are abelian groups $L,A$, with $A$ finitely generated, a surjective homomorphism $q:L\to A$, an action $\rho:G(K)\to\operatorname{Aut}(L)$ preserving $\ker q$, and classes $c_i\in L$ indexed by the projective factors.
--
--   There are a set $C$, a twist action $\sigma:L\to\operatorname{Perm}(C)$, a dimension function $d:C\to\mathbb N$, Euler values $e:C\to\mathbb Q$, and an exact-triple predicate
--   $$S\subseteq C\times C\times(C\sqcup\{\mathbf0\}).$$
--   The extra symbol represents a zero cokernel; twists fix it and its Euler value is zero. Whenever $S(k,a,Q)$ holds, for every $l\in L$ we have
--   $$S(\sigma_l k,\sigma_l a,\sigma_l Q),\qquad e(a)=e(k)+e(Q).$$
--   For every $l\in L$ and $a\in C$ there are $k\in C$ and cokernels $Q,Q'$ with
--   $$S(k,a,Q),\qquad S(k,\sigma_l a,Q'),$$
--   where each cokernel belonging to $C$ has dimension strictly less than $d(a)$.
--
--   There is an indexed collection of connected topological spaces $T_j$, points $s_j,t_j\in T_j$, and maps $p_j:T_j\to L$ such that
--   $$\ker q=\operatorname{span}_{\mathbb Z}\{p_j(t_j)-p_j(s_j):j\}.$$
--   For each $j$, $a\in C$ and $x\in T_j$, there is an open neighborhood $U\subseteq T_j$ of $x$, a finitely supported function $r:\mathbb Z\to\mathbb N$, and for every $z\in U$ a cochain complex $V_z^\bullet$ of $K$-vector spaces such that
--   $$\dim_K V_z^m=r(m)<\infty\quad(m\in\mathbb Z),\qquad
--    e(\sigma_{p_j(z)}a)=\sum_m(-1)^m\dim_K H^m(V_z^\bullet).$$
--   Thus the terms have fixed dimensions and vanish outside a common finite set of degrees on $U$. The differentials and their ranks may vary with $z$. The neighborhood, rank vector and complexes may depend on $j,a,x$. No topology on $L$ or continuity of $p_j$ is required. The complexes have actual square-zero differentials, and their homology is cycles modulo boundaries.
--
--   For each closed subset $V\subseteq X$ there is $a_V\in C$ with
--   $$d(a_V)\le d_V,\qquad d_V=\deg\operatorname{HP}(V),$$
--   where the Hilbert polynomial comes from the actual multigraded coordinate quotient. For every $g\in G(K)$ and every tuple $D_i\ge1$, eventually for natural numbers $n$,
--   $$e\!\left(\sigma_{\,n\rho_{-g}(\sum_iD_ic_i)}a_V\right)
--   =\operatorname{HF}_{\tau_g(V)}(nD).$$
--   The right side is the dimension of the indicated component of the actual ambient homogeneous coordinate quotient. The data are shared by all closed subsets; the generator and eventual threshold may vary. Empty subsets and dimension zero are included.
--
--   **Formalization Note.** This is an auxiliary geometric model with local complexes. The intended model uses coherent sheaves and families of line bundles, with bounded complexes of finite free modules computing the relevant fiber cohomology locally on a parameter space. Construction of the geometric model and these complexes, the Euler comparison, the kernel-span identity, common subobjects, finite generation of $A$ and the coordinate Hilbert comparison remain Open. The parent proves that the stated local complex data imply local constancy of the Euler values, using rank-nullity and cancellation of boundary dimensions. The complexes and their homology use Mathlib definitions; finite-dimensionality of terms and finite support are explicit hypotheses, so infinite-rank or infinite-sum default values do not supply the intended identities. No torsion-free hypothesis is imposed on $L$ or $A$. This auxiliary presentation is not a verbatim theorem from the sources.
-- source:
--   Auxiliary local-complex form of the connected-family Euler model. Stacks Project, Lemma 36.31.2, https://stacks.math.columbia.edu/tag/0BDJ , proves local constancy of the Euler function of a perfect complex by representing it locally by a bounded complex of finite free modules. Lemma 75.26.3, https://stacks.math.columbia.edu/tag/0D1Z , is its algebraic-space counterpart. Lemma 75.25.1, https://stacks.math.columbia.edu/tag/0A1P , supplies the proper flat pushforward and base-change context. The new parent proof verifies the fiberwise rank cancellation and local-constancy implication. Construction of the local complexes and their comparison with the Euler values, as well as the rest of the inherited geometric model, remain explicit Open obligations. The statement is an auxiliary formalization, not a verbatim result of these sources.

import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Cardinality
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators Topology
universe u

namespace PhilipponMultiplicity

theorem closure_action_has_local_complex_model
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
          (∃ (ι : Type u) (X : ι → Type u) (top : ∀ i, TopologicalSpace (X i))
            (s t : ∀ i, X i) (p : ∀ i, X i → L),
            (∀ i, @ConnectedSpace (X i) (top i)) ∧
            (∀ i a x, ∃ U : Set (X i), @IsOpen (X i) (top i) U ∧ x ∈ U ∧
              ∃ r : ℤ → ℕ, Function.HasFiniteSupport r ∧
              ∃ V : U → CochainComplex (ModuleCat.{u} K) ℤ,
                (∀ z j, Module.Finite K ((V z).X j)) ∧
                (∀ z j, Module.finrank K ((V z).X j) = r j) ∧
                (∀ z : U, e (σ (Multiplicative.ofAdd (p i z.val)) a) =
                  ((V z).homologyEulerChar : ℚ))) ∧
            LinearMap.ker q =
              Submodule.span ℤ (Set.range (fun i => p i (t i) - p i (s i)))) ∧
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
