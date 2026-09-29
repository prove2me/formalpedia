-- Prove2me | Theorems.Thm_PassivityTorus_power_eq
-- name    : PassivityTorus.power_eq
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-24T04:21:19.967545+00:00
-- url     : https://prove2.me/theorems/1c7966a8-91ac-41da-b81b-9bedaee07403
-- title:
--   Power identity: $P = \sum_x \sum_a v(x)\cdot(W - W^{\mathsf T})\, v(x+e_a)$
-- statement:
--   For every $q$, every $L \ge 1$, every family of real $d\times d$ link matrices $W(x,a)$ and every velocity field $v$,
--
--   $$
--   P_W(v) = \sum_{x} \sum_{a=0}^{q-1} v(x) \cdot \Bigl( \bigl(W(x,a) - W(x,a)^{\mathsf T}\bigr)\, v(x+e_a) \Bigr).
--   $$
--
--   Each link contributes to the total power only through its antisymmetric part. The identity holds for every lattice size, with no condition on the link matrices.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §6, Theorem 6.1 (extended to a q-dimensional periodic lattice): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Corrected Theorem 6.1(a) (power identity): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PassivityTorus_power

open Matrix BigOperators

namespace PassivityTorus
theorem power_eq (q L d : ℕ) [NeZero L]
    (W : Site q L → Fin q → Matrix (Fin d) (Fin d) ℝ)
    (v : Site q L → (Fin d → ℝ)) :
    power q L d W v =
      ∑ x : Site q L, ∑ a : Fin q, v x ⬝ᵥ ((W x a - (W x a)ᵀ) *ᵥ v (shift x a 1)) := by sorry
end PassivityTorus
