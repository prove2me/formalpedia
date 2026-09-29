-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_neg_conjugate_closure
-- name    : SteinitzExchange.Duality.neg_conjugate_closure
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:56:44.409578+00:00
-- url     : https://prove2.me/theorems/d6e771ae-dece-41b8-8457-26f0851fcd2c
-- title:
--   Lemma 6.1 — $(-f)^\circ(p)=-f^\bullet(-p)$ and $(-f)^\wedge=-\check f$
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be finite and nonempty and $f:B\to\mathbb R$. Then
--
--   1. $(-f)^\circ(p)=-f^\bullet(-p)$ for every $p\in\mathbb R^V$;
--   2. $(-f)^\wedge(b)=-\check f(b)$ for every $b\in\overline B$,
--
--   where $(-f)^\wedge$ is the concave closure of $-f$ and $\check f$ the convex closure of $f$.
--
--   The lemma translates statements about concave conjugates and closures into statements about convex ones; in the duality theorem it converts the M-concave closure identity of Lemma 4.5 into $\check\zeta(x)=\zeta(x)$ for M-convex $\zeta$.
--
--   **Formalization Note.** Part 2 is stated on $\overline B$, where both closures are finite; off $\overline B$ the paper's values are $-\infty=-(+\infty)$, which the real-valued closures do not represent.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 294, Lemma 6.1

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Conjugate

namespace SteinitzExchange.Duality

/-- Murota 1996, p. 294, Lemma 6.1, for any `f : B → ℝ` on a nonempty finite `B ⊆ ℤ^V`:
(1) `(−f)°(p) = −f•(−p)` for every `p ∈ ℝ^V`;
(2) `(−f)^(b) = −f̌(b)` for every `b ∈ B̄` (the closures regarded as functions on `B̄`). -/
theorem neg_conjugate_closure {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (f : (V → ℤ) → ℝ) :
    (∀ p : V → ℝ, concaveConj B (fun x => -f x) p = -convexConj B f (-p)) ∧
    (∀ b ∈ hull B, concaveClosure B (fun x => -f x) b = -convexClosure B f b) := by sorry

end SteinitzExchange.Duality
