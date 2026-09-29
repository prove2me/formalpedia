-- Prove2me | Theorems.Thm_SteinitzExchange_Extension_exc_add_linear
-- name    : SteinitzExchange.Extension.exc_add_linear
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:43:02.247222+00:00
-- url     : https://prove2.me/theorems/ce4b9b05-50f6-40a8-9c41-f6bf5edef849
-- title:
--   Theorem 2.2 — adding a linear function preserves (EXC)
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be a finite integral base set and let $\omega:B\to\mathbb R$ satisfy (EXC) (the standing assumption of Section 2.3). Then for every $p:V\to\mathbb R$ the perturbed function
--   $$\omega[p](x)=\omega(x)+\langle p,x\rangle\qquad(x\in B)$$
--   satisfies (EXC).
--
--   This is the discrete counterpart of the fact that a concave function stays concave when a linear function is added; it is what lets the maximizer characterization of Theorem 4.4 be applied to every $\omega[p]$.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 280, Section 2.3, Theorem 2.2 (standing assumption: omega satisfies (EXC))

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 280, Theorem 2.2 (under the standing assumption of §2.3 that `ω` satisfies
(EXC)): `ω[p]` satisfies (EXC) for every `p : V → ℝ`. -/
theorem exc_add_linear {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hω : SatisfiesEXC B ω) (p : V → ℝ) :
    SatisfiesEXC B (perturb ω p) := by sorry

end SteinitzExchange.Extension
