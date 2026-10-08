-- Prove2me | Theorems.Thm_WhitneyMatroid_Duality_isDual_symm
-- name    : WhitneyMatroid.Duality.isDual_symm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:44:08.242578+00:00
-- url     : https://prove2.me/theorems/dd7195a6-7a6a-4eaa-a65c-29c974b7f339
-- title:
--   Theorem 21 — duality is symmetric
-- statement:
--   Let $M$ and $M'$ be matroids on finite sets of elements. If $M'$ is a dual of $M$ (in the sense of (11.1)), then $M$ is a dual of $M'$:
--
--   $$
--   M' \text{ dual of } M \ \Longrightarrow\ M \text{ dual of } M'.
--   $$
--
--   So one may speak of $M$ and $M'$ simply as duals, as Theorems 23 and 28 do.
--
--   **Formalization Note** "Dual" is `IsDual`, (11.1) for some one-to-one correspondence between the elements; the correspondence in the conclusion may be any bijection (Whitney's proof uses the inverse of the given one).
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 522, Theorem 21

import Mathlib
import Definitions.Def_WhitneyMatroid_Duality_IsDual

namespace WhitneyMatroid.Duality

/-- Whitney, Theorem 21 (p. 522): if `M′` is a dual of `M`, then `M` is a dual of `M′`. -/
theorem isDual_symm {α β : Type*} [Finite α] [Finite β] {M : Matroid α} {M' : Matroid β}
    (h : IsDual M M') : IsDual M' M := by sorry

end WhitneyMatroid.Duality
