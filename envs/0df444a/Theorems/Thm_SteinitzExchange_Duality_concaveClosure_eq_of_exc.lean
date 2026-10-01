-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_concaveClosure_eq_of_exc
-- name    : SteinitzExchange.Duality.concaveClosure_eq_of_exc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:57:24.077527+00:00
-- url     : https://prove2.me/theorems/cabccef4-33be-49ed-b27b-5730a3a8791a
-- title:
--   Lemma 4.5 — an M-concave function coincides with its concave closure on $B$
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be a finite integral base set and let $\omega:B\to\mathbb R$ satisfy the exchange property (EXC). Then
--
--   $$\hat\omega(x)=\omega(x)\qquad\text{for all }x\in B,$$
--
--   where $\hat\omega$ is the concave closure of $\omega$.
--
--   For arbitrary $\omega$ only $\hat\omega\ge\omega$ holds on $B$; (EXC) makes the concave closure an extension of $\omega$. In the duality theorem this is what makes an integral optimum of the relaxed primal problem an optimum of the primal problem.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 288, Lemma 4.5

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Exchange
import Definitions.Def_SteinitzExchange_Duality_Conjugate

namespace SteinitzExchange.Duality

/-- Murota 1996, p. 288, Lemma 4.5: if `ω` satisfies (EXC) on the finite integral base set `B`,
then its concave closure agrees with it on `B`: `ω̂(x) = ω(x)` for all `x ∈ B`. -/
theorem concaveClosure_eq_of_exc {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hω : SatisfiesEXC B ω) :
    ∀ x ∈ B, concaveClosure B ω (toReal x) = ω x := by sorry

end SteinitzExchange.Duality
