-- Prove2me | Theorems.Thm_PhilipponMultiplicity_prime_nsmul_range_has_nonempty_interior
-- name    : PhilipponMultiplicity.prime_nsmul_range_has_nonempty_interior
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-02T08:19:22.063976+00:00
-- url     : https://prove2.me/theorems/2d05e8b7-ab00-44c3-9774-1d87ff1d82e5
-- title:
--   Prime multiplication has a Zariski-open set of divisible points
-- statement:
--   Let $G$ be a commutative algebraic group over a Philippon base field $K$ (isometrically isomorphic to $\mathbb C$ or $\mathbb C_p$), and let $\ell$ be a prime integer. The image of multiplication by $\ell$ contains a nonempty Zariski-open subset of $G(K)$:
--   $$
--   \operatorname{Int}_{\mathrm{Zar}}\{\ell x:x\in G(K)\}\ne\varnothing.
--   $$
--   Equivalently, there is a nonempty Zariski-open set $U\subseteq G(K)$ such that every point of $U$ is divisible by $\ell$ in $G(K)$. Connectedness is not assumed. This local input supports the separate checked passage to global divisibility on a connected group.
--
--   **Formalization Note.** An accepted sketch reduces this assertion to [constructibility of the multiplication image](https://prove2.me/theorems/f261158d-6367-4cda-a552-ea477d1626a6) and [nonempty interior of its Zariski closure](https://prove2.me/theorems/cfcdf389-87a6-4f85-828f-cacaed39100a). The passage from these two assertions to the original interior conclusion is proved for arbitrary topological spaces by a boundary argument. The two geometric statements in the concrete embedded-group interface remain Open. Connectedness and a regular choice of roots are not assumed; zero-dimensional groups are included.
-- source:
--   J. Garnek, Abelian varieties over p-adic fields, doctoral dissertation (2020), Lemma 1.1.2 and its differential argument, p.16: https://jgarnek.faculty.wmi.amu.edu.pl/papers/phd_final.pdf . The Stacks Project, Proposition 59.26.2(9), tag 03PA, openness of etale morphisms: https://stacks.math.columbia.edu/tag/03PA . Auxiliary local-image consequence for prime multiplication in characteristic zero, without connectedness. Constructing the multiplication morphism, proving its local etaleness, and relating its image to the concrete group-point topology remain Open.

import Definitions.Def_PhilipponMultiplicity_Geometry
set_option autoImplicit false

namespace PhilipponMultiplicity

theorem prime_nsmul_range_has_nonempty_interior
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (p : ℕ) (hp : p.Prime) :
    (@interior _ G.zariskiTopology (Set.range (fun x : G.Point => p • x))).Nonempty := by sorry

end PhilipponMultiplicity
