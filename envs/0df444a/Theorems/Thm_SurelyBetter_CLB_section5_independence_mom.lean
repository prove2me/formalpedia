-- Prove2me | Theorems.Thm_SurelyBetter_CLB_section5_independence_mom
-- name    : SurelyBetter.CLB.section5_independence_mom
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:16.910987+00:00
-- url     : https://prove2.me/theorems/e41079e1-ba67-4a44-910d-82d59f4fb1d8
-- title:
--   §5, p. 7625 — given state-by-state monotonicity, independence implies monotonicity in optimal mixtures
-- statement:
--   Let $S$ be a finite set of states, $V$ a real-valued preference functional on utility profiles $S\to\mathbb R$, and $\mathcal G$ a convex set of profiles (closed under statewise mixtures). Suppose that on $\mathcal G$:
--
--   1. $V$ satisfies **state-by-state monotonicity** (Axiom 2): $f\le f'$ statewise implies $V(f)\le V(f')$;
--   2. $V$ satisfies **independence** (Axiom 1): for all $f,g,h\in\mathcal G$ and $\alpha\in(0,1]$, $V(g)\le V(f)$ iff $V(\alpha g+(1-\alpha)h)\le V(\alpha f+(1-\alpha)h)$.
--
--   Then $V$ satisfies monotonicity in optimal mixtures restricted to $\mathcal G$: for all $f,f',g\in\mathcal G$ with $f\le f'$ statewise,
--   $$\alpha^*_{f,g}\ \le_s\ \alpha^*_{f',g},$$
--   where $\alpha^*_{f,g}$ is the set of $\alpha\in[0,1]$ maximizing $V(\alpha f+(1-\alpha)g)$ over $[0,1]$ and $\le_s$ is the set order of Definition 1.
--
--   With $\mathcal G$ the set of all profiles this is the paper's statement that, given Axiom 2, independence is a strengthening of monotonicity in optimal mixtures; in particular every subjective expected utility preference satisfies it. In the proof of Theorem 2 it is applied to preferences restricted to acts measurable with respect to $\{E,E^c\}$.
--
--   **Formalization Note** The paper argues for preferences over all acts; the statement is given for an arbitrary mixture-closed set $\mathcal G$ of profiles, the form used in the converse of Theorem 2. Convexity of $\mathcal G$ keeps the mixtures to which independence is applied inside $\mathcal G$.
-- source:
--   Ghili & Klibanoff, If It Is Surely Better, Do It More? Implications for Preferences Under Ambiguity, Management Science 67(12) (2021), p. 7625, §5 (paragraph after Axiom 2: independence and monotonicity in optimal mixtures)

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model

namespace SurelyBetter.CLB
theorem section5_independence_mom {S : Type*} [Fintype S] (V : (S → ℝ) → ℝ)
    (G : Set (S → ℝ)) (hG : Convex ℝ G) (hmon : StateMonotone V G) (hind : Independence V G) :
    MOMOn V G := by sorry
end SurelyBetter.CLB
