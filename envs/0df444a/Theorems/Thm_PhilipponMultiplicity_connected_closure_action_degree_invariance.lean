-- Prove2me | Theorems.Thm_PhilipponMultiplicity_connected_closure_action_degree_invariance
-- name    : PhilipponMultiplicity.connected_closure_action_degree_invariance
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T09:19:26.453384+00:00
-- url     : https://prove2.me/theorems/2523384d-1d5f-445b-87e8-80cbb63680a9
-- title:
--   Connected closure actions — numerical degree invariance
-- statement:
--   Let $G$ be a connected commutative algebraic group over a Philippon base field, with its given embedding in a product of projective spaces, and write $X=\overline G$ for the actual projective closure. Suppose a family of bijections $\tau_g:X\to X$ satisfies
--   $$
--   \tau_0=\mathrm{id},\qquad \tau_{g+h}=\tau_g\circ\tau_h.
--   $$
--   Every $\tau_g$ has local homogeneous polynomial presentations on $X$, and its restriction to the dense embedded group is translation by $g$. Thus each individual map is a regular automorphism, its inverse being $\tau_{-g}$.
--
--   For every closed subset $V\subseteq X$, every $g\in G$, and every positive block-degree vector $D$, prove
--   $$
--   H(V;D)=H(\tau_g(V);D).
--   $$
--   Here the two sets are viewed in the original ambient multiprojective space. $H$ is the rational degree form given by the factorial-normalized top part of the actual multigraded Hilbert polynomial of their homogeneous vanishing ideals. Arbitrary closed subsets, including reducible sets and the empty set, are allowed. The original polarization and all its block degrees remain fixed.
--
--   This is an **Open numerical invariance input** to the connected translation-degree remark preceding Philippon's Lemma 4.5, attributed there to Moreau. It is formulated after the closure maps have already been made coherent. The parent reduction proves uniqueness of the separate extensions, their identity and composition laws, inverse regularity, their homeomorphism property, the transport of closures of group subvarieties, and invariance of the vanishing ideal on passage to closure. None of those steps assumes degree invariance.
--
--   Regularity is assumed separately for each group element. Joint regularity in the group and closure variables is not an additional hypothesis: if a proof uses a connected algebraic family of automorphisms or a family argument for numerical equivalence, the required family construction must be justified from the stated data. No degree-one coordinate formula, preservation of Hilbert functions, or numerical equivalence is assumed.
--
--   **Verified divisibility and lattice reduction.** The accepted sketch proves that every homomorphism from a divisible group to a finite-rank integral general linear group is trivial. It reduces modulo each positive integer, uses Lagrange's theorem in the finite target, and detects equality of integer matrix entries by congruences.
--
--   Two geometric inputs remain Open: [divisibility of connected group points](https://prove2.me/theorems/b05cd44a-b01a-425f-8782-58dae0f9502a) and [a lattice action whose kernel preserves degree](https://prove2.me/theorems/328823ce-7049-4fe4-b8b9-eb352a153621). The latter packages the intended Néron–Severi construction and the comparison with the actual Hilbert degree. The reduction requires only the separate regular automorphisms already present in the statement.
-- source:
--   Geometric numerical-invariance input for P. Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bulletin de la SMF 114 (1986), pp.375–376, the paragraph immediately preceding Lemma 4.5, attributed to J.-C. Moreau [8]. This child states the closed-subset action formulation used by the reduction, rather than a verbatim additional numbered theorem. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree

set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

/-- The remaining numerical invariance statement for a coherent action on
the actual projective closure; individual maps are regular automorphisms. -/
theorem connected_closure_action_degree_invariance
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (hconnected : @_root_.IsConnected _ G.zariskiTopology Set.univ)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val))
    (hrestrict : ∀ (g : G.Point) (x : groupProjectiveClosure G) (y : G.Point),
      x.val = G.embedding y → (τ g x).val = G.embedding (g+y))
    (V : Set (groupProjectiveClosure G))
    (hV : @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V)
    (g : G.Point) (D : G.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) :
    SectionThree.locusDegreeValue G.ambient (Subtype.val '' V) D =
      SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D := by sorry

end PhilipponMultiplicity
