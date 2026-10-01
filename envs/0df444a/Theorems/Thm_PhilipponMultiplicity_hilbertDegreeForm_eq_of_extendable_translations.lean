-- Prove2me | Theorems.Thm_PhilipponMultiplicity_hilbertDegreeForm_eq_of_extendable_translations
-- name    : PhilipponMultiplicity.hilbertDegreeForm_eq_of_extendable_translations
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-30T15:34:52.493568+00:00
-- url     : https://prove2.me/theorems/178cf5ea-3051-4309-85ea-22317857ced6
-- title:
--   Hilbert degree is invariant under extendable translations
-- statement:
--   **Accepted proof-sketch; numerical invariance for the connected closure action remains Open.** The Lean reduction proves that the given pointwise extensions are unique on the closure, satisfy the identity and addition laws, have regular inverses, and are Zariski homeomorphisms. It identifies the transported projective closures of group subvarieties and proves that passing to closure preserves the homogeneous vanishing ideal. The sole Open child is [connected closure action degree invariance](p2m:theorem/2523384d-1d5f-445b-87e8-80cbb63680a9).
--
--   Let $K$ be one of Philippon's base fields, and let $G$ be a connected commutative algebraic group with its specified embedding in a product of projective spaces. Suppose every translation of $G$ extends to a regular self-map of its projective closure. For every locally closed subvariety $V$ of $G$, every group element $g$, and every multidegree $D$ whose coordinates are positive, the Hilbert degree forms agree:
--
--   $$H(V;D)=H(g+V;D).$$
--
--   Here $H$ is the degree form obtained from the top-dimensional part of the multigraded Hilbert polynomial of the homogeneous vanishing ideal. The extension hypothesis concerns the given embedding; it is not assumed for arbitrary embeddings.
--
--   The formal statement is unchanged. The child concerns the actual normalized Hilbert degree of closed subsets in the fixed multiprojective embedding. It assumes a coherent action with each element regular and extending its group translation. Joint regularity in the group parameter and numerical invariance are not claimed by the parent proof. Source: Philippon (1986), pp.375–376, the observation attributed to Moreau immediately preceding Lemma 4.5: https://numdam.org/articles/10.24033/bsmf.2060/ .
-- source:
--   P. Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bulletin de la SMF 114 (1986), pp. 375–376, paragraph immediately preceding Lemma 4.5 (the observation attributed to Moreau [8]). https://numdam.org/articles/10.24033/bsmf.2060/ . The formal statement makes connectedness explicit.

import Definitions.Def_PhilipponMultiplicity_Support
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem hilbertDegreeForm_eq_of_extendable_translations
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (G : EmbeddedGroupProduct K), @_root_.IsConnected _ G.zariskiTopology Set.univ →
      TranslationsExtendToClosure G →
      ∀ (V : GroupSubvariety G) (g : G.Point) (D : G.FactorIndex → ℕ),
        (∀ i, 1 ≤ D i) →
        hilbertDegreeForm G V.carrier D = hilbertDegreeForm G (translate g V.carrier) D := by sorry

end PhilipponMultiplicity
