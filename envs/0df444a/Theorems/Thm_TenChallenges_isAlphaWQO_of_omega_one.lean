-- Prove2me | Theorems.Thm_TenChallenges_isAlphaWQO_of_omega_one
-- name    : TenChallenges.isAlphaWQO_of_omega_one
-- status  : Proved
-- author  : @Davide
-- created : 2026-11-23T11:32:33.367855+00:00
-- url     : https://prove2.me/theorems/95a50330-abb4-4160-8071-4a94a1a5f703
-- title:
--   $\omega_1$-WQO implies $\alpha$-WQO for every ordinal $\alpha$
-- statement:
--   **The level $\omega_1$ decides better-quasi-ordering.** Let $Q$ be a set with an arbitrary binary relation $\le$, let $V^*_\alpha(Q)$ be the cumulative hierarchy of nonempty sets over $Q$, and let $\le^*$ be the Nash-Williams game relation on it. Recall that $(Q,\le)$ is $\alpha$-WQO when every sequence $X_0,X_1,\dots$ in $V^*_\alpha(Q)$ has indices $i<j$ with $X_i\le^* X_j$. Then for every ordinal $\alpha$
--
--   $$(Q,\le)\text{ is }\omega_1\text{-WQO}\quad\Longrightarrow\quad (Q,\le)\text{ is }\alpha\text{-WQO}.$$
--
--   Together with the monotonicity of $\alpha$-WQO in $\alpha$, this says that being $\omega_1$-WQO is equivalent to being $\alpha$-WQO for all $\alpha$, that is, to being better-quasi-ordered. It allows a statement quantified over all ordinals to be replaced by its single instance at the first uncountable ordinal.
--
--   **Formalization Note** The relation is an arbitrary `le : Q → Q → Prop`; neither reflexivity nor transitivity is assumed. Here `ω_ 1` is the first uncountable ordinal in the universe of $Q$.
-- source:
--   Ten Challenges 06 mission statement, definition of α-WQO ("BQO exactly when it is ω₁-WQO, equivalently α-WQO for every ordinal α"); Nash-Williams 1965, https://doi.org/10.1017/S0305004100039062; Georgakopoulos 2025, https://arxiv.org/abs/2510.19285

import Mathlib.SetTheory.Cardinal.Aleph
import Definitions.Def_TenChallenges_AlphaWQO

universe u

open Ordinal

namespace TenChallenges
theorem isAlphaWQO_of_omega_one {Q : Type u} (le : Q → Q → Prop) (α : Ordinal.{u}) :
    IsAlphaWQO le (ω_ 1) → IsAlphaWQO le α := by sorry
end TenChallenges
