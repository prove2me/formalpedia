-- Prove2me | Theorems.Thm_SteinitzExchange_LocalSupermod_concaveClosure_eq_of_exc
-- name    : SteinitzExchange.LocalSupermod.concaveClosure_eq_of_exc
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T15:34:50.162954+00:00
-- url     : https://prove2.me/theorems/2f8a2c6e-9ca4-42dd-a586-2feb9b1b853a
-- title:
--   Lemma 4.5 — an M-concave function coincides with its concave closure on B
-- statement:
--   Murota 1996, p. 288, Lemma 4.5. Let $B \subseteq \mathbb{Z}^V$ be a finite integral base set and let $\omega : \mathbb{Z}^V \to \mathbb{R}$ satisfy the exchange property (EXC) on $B$. Then the concave closure $\hat{\omega}$ of $\omega$ agrees with $\omega$ at every point of $B$: $\hat{\omega}(x) = \omega(x)$ for all $x \in B$. This supplies the concave-closure clause in the reverse (only-if) direction of the Local Supermodularity Theorem 5.3, and it is the hypothesis that guarantees every integer point of the hull of a maximiser set is a maximiser, which Theorem 5.1 needs.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 288, Lemma 4.5

import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Exchange
import Definitions.Def_SteinitzExchange_LocalSupermod_Localization

namespace SteinitzExchange.LocalSupermod

/-- Murota 1996, p. 288, Lemma 4.5, in the `LocalSupermod` reading: if `ω` satisfies (EXC) on the
finite integral base set `B`, then its concave closure agrees with it on `B`:
`ω̂(x) = ω(x)` for all `x ∈ B`. This is the first clause of the "only if" direction of
Theorem 5.3 (`exc_iff_localization_matroidal`). -/
theorem concaveClosure_eq_of_exc {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hω : SatisfiesEXC B ω) :
    ∀ x ∈ B, concaveClosure B ω (toReal x) = ω x := by sorry

end SteinitzExchange.LocalSupermod
