-- Prove2me | Theorems.Thm_PhilipponMultiplicity_closure_action_has_finitely_generated_degree_module
-- name    : PhilipponMultiplicity.closure_action_has_finitely_generated_degree_module
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-02T09:10:03.655754+00:00
-- url     : https://prove2.me/theorems/0a1c407f-3a18-49a0-b2d0-c638afab54ec
-- title:
--   A finitely generated divisor-class action controls degree modulo torsion
-- statement:
--   Let $G$ be a commutative algebraic group over a Philippon base field, let $X$ be its multiprojective closure, and let $\tau_g:X\to X$ be regular automorphisms satisfying $\tau_0=1$ and $\tau_{g+h}=\tau_g\circ\tau_h$. There exist a finitely generated abelian group $A$ and an action $\alpha:G(K)\to\operatorname{Aut}(A)$ such that, for every closed subset $V\subseteq X$, group element $g$, and positive block-degree vector $D$,
--   $$
--   \bigl(\alpha(g)a-a\in A_{\mathrm{tors}}\text{ for every }a\in A\bigr)
--   \quad\Longrightarrow\quad H(V;D)=H(\tau_g(V);D).
--   $$
--   Here $A_{\mathrm{tors}}$ is the subgroup of elements annihilated by a nonzero integer, and $H$ is the factorial-normalized degree form of the actual multigraded Hilbert polynomial. The same group and action work for every $V,g,D$, including empty and reducible closed subsets.
--
--   This is the geometric input for constructing a finite integral lattice action that controls degree. Torsion is permitted in $A$; no basis or action on a free group of generators is required.
--
--   **Formalization Note.** A finitely generated abelian group is represented as $\mathbb Z^m/L$ for a submodule $L$. The statement is an auxiliary consequence of the Theorem of the Base and numerical intersection theory, not a verbatim numbered theorem. Construction from the embedded-group interface and comparison with the concrete Hilbert degree remain Open. Connectedness, a joint algebraic action, and agreement with translations on the dense group are not hypotheses.
--
--   **Proof frontier.** A checked reduction leaves one [multilinear intersection model](p2m:theorem/a8435c6b-f4af-4546-8eb6-07e1f2a7f845) Open. It proves that multilinear forms with torsion-free values ignore torsion changes in their arguments, that triviality modulo torsion passes to inverse group elements, and that conjugating a finite module action to a finite free quotient preserves the same torsion-displacement condition. The remaining child constructs the geometric module and action and compares its intersection forms with the concrete Hilbert degree. The theorem's formal statement is unchanged.
-- source:
--   R. Cheng, L. Ji, M. Larson, N. Olander, Theorem of the Base, author version July 1, 2021, Lemma 2.8 (p.7), Proposition 4.3 (p.13), Lemma 7.2 and Theorem 7.4 (p.18), https://mattlarson2399.github.io/Papers/theorem-of-the-base.pdf . Stacks Project, Lemma 42.41.4 (tag 0BFI), https://stacks.math.columbia.edu/tag/0BFI , and Lemma 33.45.12 (tag 0BEY), https://stacks.math.columbia.edu/tag/0BEY . Auxiliary consequence via the finitely generated Neron-Severi group with its torsion retained and the inverse-pullback action. The embedded-scheme construction and the mixed Hilbert-degree comparison remain Open.

import Mathlib.Algebra.Module.Torsion.Basic
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree

set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem closure_action_has_finitely_generated_degree_module
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val)) :
    ∃ (m : ℕ) (L : Submodule ℤ (Fin m → ℤ))
      (α : Multiplicative G.Point →*
        (((Fin m → ℤ) ⧸ L) ≃ₗ[ℤ] ((Fin m → ℤ) ⧸ L))),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
      ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
        (∀ x, α (Multiplicative.ofAdd g) x - x ∈
          Submodule.torsion ℤ ((Fin m → ℤ) ⧸ L)) →
        SectionThree.locusDegreeValue G.ambient (Subtype.val '' V) D =
      SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D := by sorry

end PhilipponMultiplicity
