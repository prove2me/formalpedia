-- Prove2me | Theorems.Thm_PoincareFormalization_smoothConnectedSum_sdiffeomorph_of_factors
-- name    : PoincareFormalization.smoothConnectedSum_sdiffeomorph_of_factors
-- status  : Open
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T20:41:16.868596+00:00
-- url     : https://prove2.me/theorems/0cc6a0fd-e399-48cd-95b3-9429b96ff97e
-- title:
--   A smooth connected sum of two $3$-spheres is diffeomorphic to $\mathbb{S}^3$
-- statement:
--   Let $M$, $A$, and $B$ be closed connected smooth $3$-manifolds such that $M$ is a smooth connected sum $A \# B$. If both $A$ and $B$ are diffeomorphic to $\mathbb{S}^3$, then $M$ is diffeomorphic to $\mathbb{S}^3$:
--
--   $$A \simeq_{\mathrm{diff}} \mathbb{S}^3 \land B \simeq_{\mathrm{diff}} \mathbb{S}^3 \implies A \# B \simeq_{\mathrm{diff}} \mathbb{S}^3.$$
--
--   In dimension $3$, a closed smooth manifold covered by two open $3$-balls overlapping along $S^2 \times \mathbb{R}$ is diffeomorphic to $\mathbb{S}^3$ by the $3$-dimensional smooth Schoenflies theorem and Smale's theorem $\pi_0(\mathrm{Diff}^+(S^2)) = 1$.
--
--   **Formalization Note** The connected sum relation is `IsSmoothConnectedSum M A B`.
-- source:
--   J. Milnor, Lectures on the h-Cobordism Theorem (1965); A. Hatcher, A proof of the Smale conjecture, Annals of Mathematics 117 (1983), 553–607.

import Definitions.Def_PoincareFormalization_SmoothSurgery

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareFormalization

theorem smoothConnectedSum_sdiffeomorph_of_factors
    (M A B : SmoothThreeManifold) (h : IsSmoothConnectedSum M A B)
    (hA : Nonempty (A.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ S3))
    (hB : Nonempty (B.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ S3)) :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ S3) := by
  sorry

end PoincareFormalization
