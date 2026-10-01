-- Prove2me | Theorems.Thm_RockafellarMaxMono_Maximality_conj_add_halfSqNorm_finite_continuous
-- name    : RockafellarMaxMono.Maximality.conj_add_halfSqNorm_finite_continuous
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:05:02.803473+00:00
-- url     : https://prove2.me/theorems/7417c42e-cc54-43aa-8340-596ae9acbfa8
-- title:
--   §3, p. 213 — $(f+j)^*$ is finite and continuous throughout $E^*$
-- statement:
--   Let $E$ be a real Banach space, let $f$ be a lower semicontinuous proper convex function on $E$, and let $j(x) = \tfrac12\|x\|^2$. Then the conjugate $(f+j)^*$ is finite and continuous throughout $E^*$: there is a continuous real-valued function $h$ on $E^*$ (with its norm topology) such that
--
--   $$
--   (f + j)^*(x^*) = h(x^*) \qquad \text{for every } x^* \in E^* .
--   $$
--
--   This is what makes the finite-and-continuous case of Theorem A (Minty's theorem) applicable to $(f+j)^*$ on $E^*$.
--
--   **Formalization Note** "Finite and continuous" is encoded as the existence of a continuous $h : E^* \to \mathbb{R}$ whose cast to `EReal` equals $(f+j)^*$ everywhere. The paper derives this from the inf-convolution formula $(f+j)^* = f^* \,\square\, j^*$; that formula is not part of this statement.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 213, §3

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Conj
import Definitions.Def_RockafellarMaxMono_Shared_HalfSqNorm

namespace RockafellarMaxMono.Maximality

theorem conj_add_halfSqNorm_finite_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f)
    (hlsc : LowerSemicontinuous f) :
    ∃ h : StrongDual ℝ E → ℝ, Continuous h ∧
      ∀ x' : StrongDual ℝ E, Shared.conj (fun y => f y + Shared.halfSqNorm y) x' = ((h x' : ℝ) : EReal) := by sorry

end RockafellarMaxMono.Maximality
