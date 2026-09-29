-- Prove2me | Theorems.Thm_SteinitzExchange_Extension_concave_extension_imp_exc
-- name    : SteinitzExchange.Extension.concave_extension_imp_exc
-- status  : Open
-- author  : @WillR
-- created : 2026-09-28T16:53:46.416707+00:00
-- url     : https://prove2.me/theorems/ea5e435e-c0a1-4cca-88c5-fa9fe404e51a
-- title:
--   The converse of the Extension Theorem — a concave extension with integral base polytope argmaxs forces (EXC)
-- statement:
--   Let $B\subseteq \mathbb Z^V$ be a finite integral base set and $\omega:B\to\mathbb R$. Suppose there is a function $\bar\omega:\overline B\to\mathbb R$ such that
--
--   1. $\bar\omega$ is concave on $\overline B$;
--   2. $\bar\omega(x)=\omega(x)$ for all $x\in B$;
--   3. for every $p\in\mathbb R^V$, the maximizers over $\overline B$ of $\bar\omega[p](b)=\bar\omega(b)+\langle p,b\rangle$ form an integral base polytope.
--
--   Then $\omega$ satisfies the exchange property (EXC): for all $x,y\in B$ and every $u$ with $(x-y)(u)>0$ there is $v$ with $(x-y)(v)<0$, $x-\chi_u+\chi_v\in B$, $y+\chi_u-\chi_v\in B$ and
--   $$\omega(x)+\omega(y)\le \omega(x-\chi_u+\chi_v)+\omega(y+\chi_u-\chi_v).$$
--
--   This is the converse (hard) direction of Murota's Extension Theorem (1996, p. 288, Theorem 4.6). The intuition is that concavity of $\bar\omega$ plus the integrality of every maximizer face pins down the exchange inequality: if it failed at some $(x,y,u)$, a carefully chosen linear perturbation would expose a maximizing face of $\overline B$ that violates the integral base polytope condition, contradicting hypothesis 3. Proving this requires relating the exchange partner $v\in\operatorname{supp}^-(x-y)$ to an exposed face of the concave closure.
--
--   **Formalization Note.** This child isolates exactly the converse implication, so that the parent Extension Theorem reduces to Lemma 4.5 (agreement on $B$), the concavity of the concave closure, the perturbed-argmax identity, and this converse.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 288, Theorem 4.6 (converse direction)

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Extension_ConcaveClosure

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 288, Theorem 4.6 (Extension Theorem), reverse direction. Let `B ⊆ ℤ^V` be a finite
integral base set and `ω : B → ℝ` a function. Suppose `ω` extends to a concave function
`ω̄ : B̄ → ℝ` agreeing with `ω` on `B` whose maximizers over `B̄` of `ω̄[p](b) = ω̄(b) + ⟨p, b⟩`
are integral base polytopes for every `p : V → ℝ`. Then `ω` satisfies the exchange property (EXC).

This is the converse half of the Extension Theorem: the combinatorial condition on the maximizer
sets of all linear perturbations forces the base-exchange inequality
$$\omega(x) + \omega(y) \le \omega(x - \chi_u + \chi_v) + \omega(y + \chi_u - \chi_v)$$
whenever `x, y ∈ B` and `u ∈ supp⁺(x − y)`. The argument proceeds by contradiction: if the
exchange inequality fails for some `x, y, u`, one produces a linear functional `p` (a supporting
separator at a maximizing face) whose maximizer set over `B̄` cannot be an integral base polytope,
contradicting the hypothesis. -/
theorem concave_extension_imp_exc {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (ωbar : (V → ℝ) → ℝ)
    (hconc : ConcaveOn ℝ (hull B) ωbar)
    (hext : ∀ x ∈ B, ωbar (toReal x) = ω x)
    (hpoly : ∀ p : V → ℝ, IsIntegralBasePolytope (argmaxOn (hull B) (fun b => ωbar b + pairing p b))) :
    SatisfiesEXC B ω := by sorry

end SteinitzExchange.Extension
