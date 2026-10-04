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
--   **Formalization Note.** Closure and interior use the actual induced Zariski topology. A checked Lean reduction proves the derivative formula from the local unit identities, iterates the local law with neighborhood control, applies the strict inverse function theorem, and transfers local images to the Zariski closure. The proof works for every positive integer and allows dimension zero. Its sole Open input is [a local analytic addition model with Zariski-thick parameter neighborhoods](https://prove2.me/theorems/1c4c4b85-a17a-49d8-91cc-7e289621e4ed). Constructing that model from the embedded algebraic-group data remains required; the target's formal statement and hypotheses are unchanged.
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
