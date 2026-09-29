-- Prove2me | Theorems.Thm_SteinitzExchange_Extension_exc_iff_argmax_isIntegralBaseSet
-- name    : SteinitzExchange.Extension.exc_iff_argmax_isIntegralBaseSet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:45:11.053013+00:00
-- url     : https://prove2.me/theorems/92cc0338-bc2e-4441-8243-0f24a484a449
-- title:
--   Theorem 4.4 — (EXC) iff every $\operatorname{argmax}(\omega[p])$ is an integral base set
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be a finite integral base set and $\omega:B\to\mathbb R$. Then $\omega$ satisfies (EXC) if and only if, for every $p:V\to\mathbb R$,
--   $$\operatorname{argmax}(\omega[p])=\{x\in B\mid \omega(x)+\langle p,x\rangle\ge\omega(y)+\langle p,y\rangle\ \forall y\in B\}$$
--   is an integral base set (equivalently, $\overline{\operatorname{argmax}(\omega[p])}$ is an integral base polytope whose integer points are exactly $\operatorname{argmax}(\omega[p])$).
--
--   This characterizes M-concavity by its maximizers, as concavity of a function is characterized by the convexity of the maximizer sets of all its linear perturbations.
--
--   **Formalization Note.** The page states the condition as "$\overline{\operatorname{argmax}(\omega[p])}$ is an integral base polytope". Read literally (the convex hull of $\operatorname{argmax}(\omega[p])$ equals the convex hull of *some* integral base set) the "if" direction is false: on $B=\{(2,0),(1,1),(0,2)\}$ with $\omega=0,-1,0$ every $\operatorname{argmax}(\omega[p])$ is $\{(2,0)\}$, $\{(0,2)\}$ or $\{(2,0),(0,2)\}$, each with an integral base polytope as convex hull, yet (EXC) fails. The paper's proof uses that $\operatorname{argmax}(\omega[p])$ itself is an integral base set, the reading glossed in Lemma 4.3 and used when Theorem 4.4 is applied on p. 292; that reading is stated here.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 286, Theorem 4.4 (read as in Lemma 4.3, p. 285, and as applied on p. 292)

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 286, Theorem 4.4, in the reading of Lemma 4.3 ("argmax(ω) is an integral base
set, that is, conv(argmax(ω)) is an integral base polytope"): on a finite integral base set `B`,
`ω` satisfies (EXC) iff `argmax(ω[p])` is an integral base set for every `p : V → ℝ`. -/
theorem exc_iff_argmax_isIntegralBaseSet {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) :
    SatisfiesEXC B ω ↔ ∀ p : V → ℝ, IsIntegralBaseSet (argmaxB B (perturb ω p)) := by sorry

end SteinitzExchange.Extension
