-- Prove2me | Theorems.Thm_PhilipponMultiplicity_prime_nsmul_range_closure_has_nonempty_interior
-- name    : PhilipponMultiplicity.prime_nsmul_range_closure_has_nonempty_interior
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-02T11:04:29.559353+00:00
-- url     : https://prove2.me/theorems/cfcdf389-87a6-4f85-828f-cacaed39100a
-- title:
--   The closure of a prime multiplication image has nonempty interior
-- statement:
--   Let $G$ be a commutative algebraic group over a Philippon base field $K$, and let $p$ be a prime integer. The Zariski closure of the multiplication image contains a nonempty open subset:
--   $$\operatorname{Int}_{\mathrm{Zar}}\!\left(\overline{\{p x:x\in G(K)\}}^{\mathrm{Zar}}\right)\ne\varnothing.$$
--   This is the local dominance input for prime multiplication. It does not require the image to be dense in every connected component. Together with constructibility of the image, it yields a nonempty open set of divisible points. Connectedness is not assumed, and zero-dimensional groups are included.
--
--   **Formalization Note.** Closure and interior are both taken in the actual induced Zariski topology on the repository's embedded group points. This auxiliary consequence of the characteristic-zero differential argument is not a verbatim numbered source theorem. Establishing the local dimension or dominance statement in the embedded-group interface remains Open.
-- source:
--   J. Garnek, Abelian varieties over p-adic fields, doctoral dissertation (2020), Lemma 1.1.2 and its differential/dimension argument, p.16, https://jgarnek.faculty.wmi.amu.edu.pl/papers/phd_final.pdf . Auxiliary local-dominance consequence for a possibly disconnected group: the differential of multiplication by p is scalar multiplication by p in characteristic zero. Only nonempty interior of the image closure is asserted. The comparison with the actual embedded-group Zariski topology remains Open.

import Mathlib.Topology.Constructible
import Definitions.Def_PhilipponMultiplicity_Geometry
set_option autoImplicit false

namespace PhilipponMultiplicity

theorem prime_nsmul_range_closure_has_nonempty_interior
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (p : ℕ) (hp : p.Prime) :
    (@interior _ G.zariskiTopology
      (@closure _ G.zariskiTopology (Set.range (fun x : G.Point => p • x)))).Nonempty := by sorry

end PhilipponMultiplicity
