-- Prove2me | Theorems.Thm_SocialEquilibrium_Existence_fixed_point_of_contractible_polyhedron
-- name    : SocialEquilibrium.Existence.fixed_point_of_contractible_polyhedron
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:42:35.091458+00:00
-- url     : https://prove2.me/theorems/fd58b687-6c22-454b-9a7e-c686f4a2db2f
-- title:
--   LEMMA — a semicontinuous map with contractible values on a contractible polyhedron has a fixed point
-- statement:
--   Let $Z$ be a contractible polyhedron in a finite-dimensional real normed space, and let $\phi$ be a multi-valued function from $Z$ to $Z$ that is **semicontinuous** (its graph $\{(z,z')\mid z'\in\phi(z)\}$ is closed in $Z\times Z$) and such that $\phi(z)$ is contractible for every $z\in Z$. Then $\phi$ has a fixed point:
--   $$\exists\, z^*\in Z,\qquad z^*\in\phi(z^*).$$
--
--   Debreu uses this particular case of the fixed-point theorem of Eilenberg and Montgomery (1946), or of Begle's more general result, as the lemma of the existence proof. It generalizes Kakutani's fixed-point theorem, which assumes a convex compact domain and convex values.
--
--   **Formalization Note** Contractibility of $\phi(z)$ includes nonemptiness. $\phi(z)$ is a subset of the subtype $Z$ and carries the subspace topology.
-- source:
--   Debreu, A Social Equilibrium Existence Theorem, Proc. Natl. Acad. Sci. USA 38(10), 1952, p. 889, LEMMA (with the definitions of semicontinuous and fixed point on pp. 888-889)

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsPolyhedron
import Definitions.Def_SocialEquilibrium_Existence_IsContractible
import Definitions.Def_SocialEquilibrium_Existence_graph

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §2, p. 889, LEMMA (a particular case of the Eilenberg–Montgomery fixed point
theorem): let `Z` be a contractible polyhedron and `φ` a semicontinuous (closed-graph)
multi-valued function from `Z` to `Z` such that `φ(z)` is contractible for every `z ∈ Z`. Then
`φ` has a fixed point `z* ∈ φ(z*)`. -/
theorem fixed_point_of_contractible_polyhedron {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (hZ : IsPolyhedron Z) (hZc : IsContractible Z)
    (φ : Z → Set Z) (hφ : IsSemicontinuous φ) (hφc : ∀ z, IsContractible (φ z)) :
    ∃ z, z ∈ φ z := by sorry

end SocialEquilibrium.Existence
