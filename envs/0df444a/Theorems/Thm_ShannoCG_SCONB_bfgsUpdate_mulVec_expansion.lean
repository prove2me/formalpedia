-- Prove2me | Theorems.Thm_ShannoCG_SCONB_bfgsUpdate_mulVec_expansion
-- name    : ShannoCG.SCONB.bfgsUpdate_mulVec_expansion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T07:07:40.997223+00:00
-- url     : https://prove2.me/theorems/dd8e1bed-9bad-43dc-be58-6b2d29d8d71f
-- title:
--   Eq. (34): the two-update direction without stored matrices
-- statement:
--   Let $\hat H_k$ be any real $n\times n$ matrix and $p_k, y_k, g_{k+1} \in \mathbb R^n$, and let $\hat H_{k+1}$ be the BFGS update of $\hat H_k$ with $(p_k, y_k)$. Then the direction $d_{k+1} = -\hat H_{k+1} g_{k+1}$ satisfies
--
--   $$d_{k+1} = -\hat H_k g_{k+1} + \frac{p_k' g_{k+1}}{p_k' y_k}\, \hat H_k y_k - \left(\left(1 + \frac{y_k' \hat H_k y_k}{p_k' y_k}\right)\frac{p_k' g_{k+1}}{p_k' y_k} - \frac{y_k' \hat H_k g_{k+1}}{p_k' y_k}\right) p_k.$$
--
--   The identity shows that the direction only requires the vectors $\hat H_k g_{k+1}$ and $\hat H_k y_k$ and a few inner products, so no matrix needs to be stored. It is the starting point of the proof that the double-update methods reduce to Beale's method on a quadratic.
--
--   **Formalization Note** Stated for an arbitrary matrix and arbitrary vectors, with no hypothesis on $p_k'y_k$: both sides use the same (total) quotients.
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, DOI 10.1287/moor.3.3.244, p. 250 (PDF p. 7), §IV, eq. (34)

import Mathlib
import Definitions.Def_ShannoCG_SCONB_bfgsUpdate

open Matrix

namespace ShannoCG.SCONB

/-- Shanno, *Conjugate Gradient Methods with Inexact Searches*, Math. Oper. Res. 3(3) (1978), §IV, p. 250 (PDF 7), eq. (34): for every matrix `Ĥ_k` and vectors `p_k, y_k, g_{k+1}`,
the direction `d_{k+1} = −Ĥ_{k+1} g_{k+1}` with `Ĥ_{k+1}` the update (32) expands as
`d_{k+1} = −Ĥ_k g_{k+1} + (p_k' g_{k+1} / p_k' y_k) Ĥ_k y_k
  − ((1 + y_k' Ĥ_k y_k / p_k' y_k)(p_k' g_{k+1} / p_k' y_k) − y_k' Ĥ_k g_{k+1} / p_k' y_k) p_k`.

**Formalization Note.** Stated generically (no quadratic, no symmetry of `H`), as the paper uses
it. No hypothesis on `p ⬝ᵥ y` is needed: both sides use the same (total) quotients. -/
theorem bfgsUpdate_mulVec_expansion {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (p y g : Fin n → ℝ) :
    -(bfgsUpdate H p y *ᵥ g) =
      -(H *ᵥ g) + ((p ⬝ᵥ g) / (p ⬝ᵥ y)) • (H *ᵥ y)
        - ((1 + (y ⬝ᵥ (H *ᵥ y)) / (p ⬝ᵥ y)) * ((p ⬝ᵥ g) / (p ⬝ᵥ y))
            - (y ⬝ᵥ (H *ᵥ g)) / (p ⬝ᵥ y)) • p := by sorry

end ShannoCG.SCONB
