-- Prove2me | Theorems.Thm_RockafellarMaxMono_Cyclic_conj_add_halfSqNorm_finite_continuous
-- name    : RockafellarMaxMono.Cyclic.conj_add_halfSqNorm_finite_continuous
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:13:25.740989+00:00
-- url     : https://prove2.me/theorems/72b042d5-fc79-4baa-912b-29ca6c1ddfeb
-- title:
--   §3, p. 213 — $(f + j)^*$ is finite and continuous throughout $E^*$
-- statement:
--   Let $E$ be a real Banach space with dual $E^*$, let $f$ be a lower semicontinuous proper convex function on $E$, and let $j(x) = \tfrac12\|x\|^2$. Then the conjugate function
--
--   $$
--   (f + j)^*(x^*) = \sup \{\, \langle x, x^* \rangle - f(x) - j(x) \mid x \in E \,\}
--   $$
--
--   is finite and continuous throughout $E^*$: there is a continuous function $h : E^* \to \mathbb{R}$ with $(f+j)^*(x^*) = h(x^*)$ for every $x^* \in E^*$.
--
--   The paper deduces this from the formula $(f + j)^* = f^* \mathbin{\square} j^*$ (infimal convolution, with $j^*(x^*) = \tfrac12\|x^*\|^2$). In the proof of Theorem B it lets the finite continuous case be applied to $(f+j)^*$ and $(g+j)^*$ on $E^*$.
--
--   **Formalization Note** "Finite" means the `EReal`-valued conjugate coincides everywhere with a real-valued function; continuity is in the norm topology of $E^*$. The infimal-convolution formula of the same sentence is not part of this statement.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 213, §3

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Conj
import Definitions.Def_RockafellarMaxMono_Shared_HalfSqNorm

namespace RockafellarMaxMono.Cyclic

theorem conj_add_halfSqNorm_finite_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f)
    (hlsc : LowerSemicontinuous f) :
    ∃ h : StrongDual ℝ E → ℝ, Continuous h ∧
      ∀ x' : StrongDual ℝ E, Shared.conj (fun y => f y + Shared.halfSqNorm y) x' = ((h x' : ℝ) : EReal) := by sorry

end RockafellarMaxMono.Cyclic
