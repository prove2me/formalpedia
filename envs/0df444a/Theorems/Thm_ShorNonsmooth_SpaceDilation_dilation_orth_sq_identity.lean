-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_dilation_orth_sq_identity
-- name    : ShorNonsmooth.SpaceDilation.dilation_orth_sq_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T20:24:08.174823+00:00
-- url     : https://prove2.me/theorems/84914d46-4de7-4167-b8ce-240305a09636
-- title:
--   The dilation $R_a(\xi)$ acts as $a$ along $\xi$ and as the identity on $\xi^\perp$ (Shor 1985, p. 56)
-- statement:
--   For the dilation operator $R_a(\xi) = I + (a-1)S$ of Shor (1985) — the map that scales the direction $\xi$ by $a$ and acts as the identity on $\xi^\perp$ — one has
--
--   $$\|R_a(\xi)(c\,\xi + w)\|^2 = a^2c^2 + \|w\|^2 \qquad (w \perp \xi, \ \|\xi\| = 1).$$
--
--   That is, $R_a(\xi)$ multiplies the $\xi$-component of a vector by $a$ and leaves the orthogonal component alone. This is the structural fact behind the one-step estimate in Theorem 3.3 (pp. 56-57): applying $\alpha_{k+1}$ to a vector whose $\xi_k$-component is $\gamma_k - h_{k+1}$ and whose orthogonal remainder is $w_k$ yields squared norm $\alpha_{k+1}^2(\gamma_k - h_{k+1})^2 + \|w_k\|^2$. It packages the two Pythagoras applications that the proof performs at the dilation step.
-- source:
--   Shor, Extensions of Subgradient Methods for Minimization (1985), pp. 55-56: $R_\alpha(\xi)$ acts as $x \mapsto \alpha\langle x,\xi\rangle\xi + (x - \langle x,\xi\rangle\xi)$, i.e. scaling along $\xi$ and identity on $\xi^\perp$.

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

open ShorNonsmooth.SpaceDilation

namespace ShorNonsmooth.SpaceDilation

/-- If `w` is orthogonal to a unit vector `ξ` then
`‖dilation a ξ (c • ξ + w)‖ ^ 2 = a ^ 2 * c ^ 2 + ‖w‖ ^ 2` for any `a`, `c`. -/
theorem dilation_orth_sq_identity {n : ℕ} (a c : ℝ)
    (ξ w : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ = 1) (horth : inner ℝ w ξ = 0) :
    ‖dilation a ξ (c • ξ + w)‖ ^ 2 = a ^ 2 * c ^ 2 + ‖w‖ ^ 2 := by
  sorry

end ShorNonsmooth.SpaceDilation
