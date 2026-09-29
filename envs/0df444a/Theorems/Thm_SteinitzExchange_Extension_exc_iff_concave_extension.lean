-- Prove2me | Theorems.Thm_SteinitzExchange_Extension_exc_iff_concave_extension
-- name    : SteinitzExchange.Extension.exc_iff_concave_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:46:12.773543+00:00
-- url     : https://prove2.me/theorems/a7631793-cb78-43a3-8f96-335da61dd29a
-- title:
--   Theorem 4.6 (Extension Theorem) — (EXC) iff a concave extension to $\overline B$ with integral base polytope maximizers
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be a finite integral base set, $\overline B$ its convex hull, and $\omega:B\to\mathbb R$. Then $\omega$ satisfies the exchange property (EXC) if and only if there is a function $\bar\omega:\overline B\to\mathbb R$ such that
--
--   1. $\bar\omega$ is concave on $\overline B$;
--   2. $\bar\omega$ extends $\omega$: $\bar\omega(x)=\omega(x)$ for all $x\in B$;
--   3. for every $p:V\to\mathbb R$, the set of maximizers over $\overline B$ of $\bar\omega[p](b)=\bar\omega(b)+\langle p,b\rangle$,
--   $$\operatorname{argmax}(\bar\omega[p])=\{b\in\overline B\mid \bar\omega(b)+\langle p,b\rangle\ge\bar\omega(c)+\langle p,c\rangle\ \forall c\in\overline B\},$$
--   is an integral base polytope (the convex hull of a finite integral base set; in particular nonempty).
--
--   This is the paper's precise statement of "M-concavity = concavity + integrality": it identifies the exchange property with concave extendability together with a combinatorial condition on the maximizer sets of all linear perturbations.
--
--   **Formalization Note.** $\bar\omega$ is a total function on $\mathbb R^V$, but concavity is required only on $\overline B$ and the argmax ranges only over $\overline B$, so its values outside $\overline B$ do not matter. No upper semicontinuity is assumed; if some $\bar\omega[p]$ has no maximizer on $\overline B$, condition 3 fails, as in the paper (an integral base polytope is nonempty).
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 288, Theorem 4.6 (Extension Theorem)

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Extension_ConcaveClosure

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 288, Theorem 4.6 (Extension Theorem): `ω : B → ℝ` on a finite integral base
set `B` satisfies (EXC) iff it extends to a concave function `ω̄ : B̄ → ℝ` (concave on `B̄`,
equal to `ω` on `B`) such that `argmax(ω̄[p])`, taken over `B̄`, is an integral base polytope
for every `p : V → ℝ`. Only the values of `ω̄` on `B̄` enter. -/
theorem exc_iff_concave_extension {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) :
    SatisfiesEXC B ω ↔
      ∃ ωbar : (V → ℝ) → ℝ, ConcaveOn ℝ (hull B) ωbar ∧
        (∀ x ∈ B, ωbar (toReal x) = ω x) ∧
        ∀ p : V → ℝ,
          IsIntegralBasePolytope (argmaxOn (hull B) (fun b => ωbar b + pairing p b)) := by sorry

end SteinitzExchange.Extension
