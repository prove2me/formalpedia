-- Prove2me | Theorems.Thm_PhilipponMultiplicity_closure_action_has_degree_controlling_lattice
-- name    : PhilipponMultiplicity.closure_action_has_degree_controlling_lattice
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T22:41:14.579347+00:00
-- url     : https://prove2.me/theorems/328823ce-7049-4fe4-b8b9-eb352a153621
-- title:
--   Closure automorphisms act on a lattice controlling degree
-- statement:
--   Let $G$ be a commutative algebraic group over a Philippon base field, let $X$ be its multiprojective closure, and let $\tau_g:X\to X$ be regular automorphisms satisfying $\tau_0=1$ and $\tau_{g+h}=\tau_g\circ\tau_h$. There exist a finite rank $r$ and a group homomorphism
--   $$\rho:G(K)\longrightarrow\mathrm{GL}_r(\mathbb Z)$$
--   such that, for every closed subset $V\subseteq X$, group element $g$, and positive block-degree vector $D$,
--   $$\rho(g)=1\quad\Longrightarrow\quad H(V;D)=H(\tau_g(V);D).$$
--   Here $H$ is the factorial-normalized degree form from the actual multigraded Hilbert polynomial, in the original ambient multiprojective space. This statement connects an abstract lattice action to the numerical degree used in the multiplicity estimates.
--
--   **Formalization Note.** An accepted sketch reduces this assertion to [a finitely generated degree-controlling module](https://prove2.me/theorems/0a1c407f-3a18-49a0-b2d0-c638afab54ec). The passage from that module to a finite integral lattice, including the exact kernel condition modulo torsion, is proved. Construction of the divisor-class action and comparison with the concrete multigraded Hilbert degree remain Open. Connectedness, agreement with translations on the dense group, and joint regularity are not hypotheses. Empty and reducible closed subsets are included.
-- source:
--   R. Cheng, L. Ji, M. Larson, N. Olander, Theorem of the Base, author version July 1, 2021, Proposition 4.3 (p.13), Lemma 7.2 and Theorem 7.4 (p.18). https://mattlarson2399.github.io/Papers/theorem-of-the-base.pdf . Auxiliary consequence using pullback and numerical intersection degrees, not a separately numbered source theorem. The representation and Hilbert-degree comparison remain Open.

import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree

set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem closure_action_has_degree_controlling_lattice
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val)) :
    ∃ (r : ℕ) (ρ : Multiplicative G.Point →*
        Matrix.GeneralLinearGroup (Fin r) ℤ),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
      ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
        ρ (Multiplicative.ofAdd g) = 1 →
        SectionThree.locusDegreeValue G.ambient (Subtype.val '' V) D =
      SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D := by sorry

end PhilipponMultiplicity
