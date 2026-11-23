-- Prove2me | Theorems.Thm_TenChallenges_challenge_06_all_graphs_omega_one
-- name    : TenChallenges.challenge_06_all_graphs_omega_one
-- status  : Open
-- author  : @Davide
-- created : 2026-11-23T11:32:28.861277+00:00
-- url     : https://prove2.me/theorems/c02927a3-e195-4974-afbb-7e5b9485b627
-- title:
--   Finite graphs are $\omega_1$-WQO under minors
-- statement:
--   **The better-quasi-ordering conjecture for graph minors, at the single level $\omega_1$.** Let $\mathcal G_{\mathrm{fin}}$ be the class of finite simple graphs, ordered by the minor relation $\preceq$. Then $\mathcal G_{\mathrm{fin}}$ is $\omega_1$-well-quasi-ordered:
--
--   $$(V^*_{\omega_1}(\mathcal G_{\mathrm{fin}}),\le^*)\ \text{is well-quasi-ordered}.$$
--
--   Equivalently, for every sequence $X_0,X_1,\dots$ of elements of countable levels of the hierarchy over finite graphs there are $i<j$ with $X_i\le^* X_j$. This is an open conjecture: it is equivalent to finite graphs being better-quasi-ordered under minors, and it contains the Graph Minor Theorem.
--
--   **Formalization Note** `ω_ 1` is the first uncountable ordinal.
-- source:
--   Ten Challenges 06 mission statement, definition of α-WQO ("BQO exactly when it is ω₁-WQO, equivalently α-WQO for every ordinal α"); Nash-Williams 1965, https://doi.org/10.1017/S0305004100039062; Georgakopoulos 2025, https://arxiv.org/abs/2510.19285

import Mathlib.SetTheory.Cardinal.Aleph
import Definitions.Def_TenChallenges_AlphaWQO

open Ordinal

namespace TenChallenges
theorem challenge_06_all_graphs_omega_one : IsAlphaWQO FiniteGraph.MinorLE (ω_ 1) := by sorry
end TenChallenges
