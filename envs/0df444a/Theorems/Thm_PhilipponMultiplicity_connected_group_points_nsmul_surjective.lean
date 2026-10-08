-- Prove2me | Theorems.Thm_PhilipponMultiplicity_connected_group_points_nsmul_surjective
-- name    : PhilipponMultiplicity.connected_group_points_nsmul_surjective
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T22:40:44.598115+00:00
-- url     : https://prove2.me/theorems/b05cd44a-b01a-425f-8782-58dae0f9502a
-- title:
--   Divisibility of connected commutative group points
-- statement:
--   Let $G$ be a connected commutative algebraic group over a Philippon base field $K$ (isometrically isomorphic to $\mathbb C$ or $\mathbb C_p$). For every positive integer $n$, multiplication by $n$ is surjective on $G(K)$:
--   $$\forall g\in G(K),\quad\exists h\in G(K),\quad nh=g.$$
--
--   This divisibility property lets the degree-invariance reduction rule out nontrivial actions of the point group on finite groups and finite-rank integral lattices.
--
--   **Formalization Note.** The group is the actual finite product of locally closed embedded groups, and connectedness uses its induced Zariski topology. This is the characteristic-zero specialization of Garnek, Lemma 1.1.2, expressed in the repository's embedded-group interface. Its geometric proof in that interface remains Open. No division operation is included in the definitions.
--
--   **Verified local-to-global reduction.** The accepted sketch proves that nonempty interior of a homomorphism's image implies surjectivity into a connected group with continuous translations. It reuses the actual polynomial translation-continuity proofs for the Zariski topology and proves that prime divisibility implies divisibility by every positive integer.
--
--   The sole Open dependency is [local prime divisibility](https://prove2.me/theorems/2d05e8b7-ab00-44c3-9774-1d87ff1d82e5): each prime multiplication image must contain a nonempty Zariski-open set. This geometric child does not assume connectedness, global divisibility, or a regular choice of roots. Its construction remains Open; propagation through connectedness and prime factors is proved.
-- source:
--   J. Garnek, Abelian varieties over p-adic fields, doctoral dissertation, Adam Mickiewicz University (2020), Lemma 1.1.2 and its differential proof, p.16. https://jgarnek.faculty.wmi.amu.edu.pl/papers/phd_final.pdf . Characteristic-zero specialization to Philippon base fields and the repository embedded-group interface; not a verbatim transcription.

import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree

set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem connected_group_points_nsmul_surjective
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (hconnected : @_root_.IsConnected _ G.zariskiTopology Set.univ) :
    ∀ n : ℕ, 0 < n → Function.Surjective (fun g : G.Point => n • g) := by sorry

end PhilipponMultiplicity
