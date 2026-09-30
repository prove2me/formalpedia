-- Prove2me | Theorems.Thm_SeymourMFMC_Binary_minor_of_mengerian
-- name    : SeymourMFMC.Binary.minor_of_mengerian
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T04:01:50.285928+00:00
-- url     : https://prove2.me/theorems/9c07b7d1-4e65-4583-ba8c-76ebfde47922
-- title:
--   (2.3) — every minor of a Mengerian clutter is Mengerian
-- statement:
--   Let $\mathbf L$ be a clutter. If $\mathbf L$ is Mengerian, then every minor $\mathbf L'$ of $\mathbf L$, obtained by any finite sequence of deletions $\mathbf L_1 \mapsto \mathbf L_1 \setminus Z$ and contractions $\mathbf L_1 \mapsto \mathbf L_1 / Z$, is Mengerian:
--
--   $$
--   \mathbf L \text{ Mengerian},\ \mathbf L' \preceq \mathbf L \ \Longrightarrow\ \mathbf L' \text{ Mengerian}.
--   $$
--
--   The Mengerian property is thus closed under minors, which is what makes an excluded-minor characterization possible. Together with the fact that $Q_6$ is not Mengerian, it gives the easy direction of the main theorem.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 194, (2.3)

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_IsClutter
import Definitions.Def_SeymourMFMC_Binary_IsMengerian
import Definitions.Def_SeymourMFMC_Binary_IsMinor

namespace SeymourMFMC.Binary

/-- Seymour 1977, (2.3), p. 194: if `L` is Mengerian, so are all its minors. -/
theorem minor_of_mengerian {α : Type*} [DecidableEq α] (L L' : Finset (Finset α))
    (hL : IsClutter L) (hM : IsMengerian L) (hminor : IsMinor L' L) :
    IsMengerian L' := by sorry

end SeymourMFMC.Binary
