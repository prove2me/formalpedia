-- Prove2me | Theorems.Thm_SteinitzExchange_Extension_concaveClosure_eq_of_exc
-- name    : SteinitzExchange.Extension.concaveClosure_eq_of_exc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:45:45.08088+00:00
-- url     : https://prove2.me/theorems/a597929f-571c-4f6d-8a25-258d1a8a54ac
-- title:
--   Lemma 4.5 — an M-concave function coincides with its concave closure on $B$
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be a finite integral base set. If $\omega:B\to\mathbb R$ has the exchange property (EXC), then its concave closure $\hat\omega$ satisfies
--   $$\hat\omega(x)=\omega(x)\qquad\text{for all }x\in B.$$
--
--   By Lemma 4.1(1) one always has $\hat\omega\ge\omega$ on $B$; (EXC) forces equality, so $\hat\omega$ is a concave extension of $\omega$ to $\overline B$. This is the concave extension used in the "only if" direction of the Extension Theorem.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 288, Lemma 4.5

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Extension_ConcaveClosure

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 288, Lemma 4.5: if `ω` satisfies (EXC) on the finite integral base set `B`,
then its concave closure agrees with it on `B`: `ω̂(x) = ω(x)` for all `x ∈ B`. -/
theorem concaveClosure_eq_of_exc {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hω : SatisfiesEXC B ω) :
    ∀ x ∈ B, concaveClosure B ω (toReal x) = ω x := by sorry

end SteinitzExchange.Extension
