-- Prove2me | Theorems.Thm_SteinitzExchange_LocalSupermod_exc_iff_argmax_isIntegralBaseSet
-- name    : SteinitzExchange.LocalSupermod.exc_iff_argmax_isIntegralBaseSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:50:49.540992+00:00
-- url     : https://prove2.me/theorems/6af23d2a-2fda-4271-b3fc-e5b61bf9415e
-- title:
--   Theorem 4.4 — (EXC) holds iff every argmax(ω[p]) is an integral base set
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be a finite integral base set and $\omega:B\to\mathbb R$. Then
--
--   $$\omega\ \text{satisfies (EXC)}\iff\operatorname{argmax}(\omega[p])\ \text{satisfies (B1) for every}\ p\in\mathbb R^V,$$
--
--   where $\omega[p](x)=\omega(x)+\langle p,x\rangle$. (Each $\operatorname{argmax}(\omega[p])$ is finite and nonempty.)
--
--   The theorem characterizes M-concavity by the combinatorial shape of the maximizer sets of all linear perturbations; combined with Theorem 5.1 it links (EXC) to "matroidal" localizations.
--
--   **Formalization Note.** The paper phrases the condition as "$\overline{\operatorname{argmax}(\omega[p])}$ is an integral base polytope". This is formalized as "$\operatorname{argmax}(\omega[p])$ is a finite integral base set", the reading fixed by the paper's Lemma 4.3 ("argmax(ω) is an integral base set, that is, …") and used in the proof of Theorem 5.3. The literal convex-hull reading makes the "if" direction false (e.g. $B=\{(2,0),(1,1),(0,2)\}$, $\omega=(0,-10,0)$: every convex hull of a maximizer set is an integral base polytope, yet (EXC) fails). The same statement appears in the first mission of this series.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 286, Theorem 4.4 (reading from Lemma 4.3, p. 285)

import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Exchange

namespace SteinitzExchange.LocalSupermod

/-- Murota 1996, p. 286, Theorem 4.4, in the reading of Lemma 4.3 ("argmax(ω) is an integral base
set, that is, conv(argmax(ω)) is an integral base polytope"): on a finite integral base set `B`,
`ω` satisfies (EXC) iff `argmax(ω[p])` is an integral base set for every `p : V → ℝ`. -/
theorem exc_iff_argmax_isIntegralBaseSet {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) :
    SatisfiesEXC B ω ↔ ∀ p : V → ℝ, IsIntegralBaseSet (argmaxB B (perturb ω p)) := by sorry

end SteinitzExchange.LocalSupermod
