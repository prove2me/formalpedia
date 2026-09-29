-- Prove2me | Theorems.Thm_SteinitzExchange_Extension_argmax_isIntegralBaseSet
-- name    : SteinitzExchange.Extension.argmax_isIntegralBaseSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:43:36.257648+00:00
-- url     : https://prove2.me/theorems/d45d98cb-334c-407d-9fd6-ffcd4090958c
-- title:
--   Lemma 4.3 — the maximizers of an M-concave function form an integral base set
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be a finite integral base set. If $\omega:B\to\mathbb R$ has the exchange property (EXC), then
--   $$\operatorname{argmax}(\omega)=\{x\in B\mid \omega(x)\ge\omega(y)\ \forall y\in B\}$$
--   is an integral base set, that is, its convex hull $\overline{\operatorname{argmax}(\omega)}$ is an integral base polytope.
--
--   This is the discrete analogue of the convexity of the set of maximizers of a concave function.
--
--   **Formalization Note.** The Lean conclusion is that $\operatorname{argmax}(\omega)$ is a finite integral base set (nonempty, with (B1)), the reading the page glosses with "that is".
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 285, Lemma 4.3

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 285, Lemma 4.3: if `ω` satisfies (EXC) on the finite integral base set `B`,
then `argmax(ω)` is an integral base set. -/
theorem argmax_isIntegralBaseSet {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hω : SatisfiesEXC B ω) :
    IsIntegralBaseSet (argmaxB B ω) := by sorry

end SteinitzExchange.Extension
