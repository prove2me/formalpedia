-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_lemma_4_2
-- name    : StrictCompatLB.MeanField.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:50:47.754261+00:00
-- url     : https://prove2.me/theorems/6e2944de-613a-487c-838d-923ec7d0c4bc
-- title:
--   Lemma 4.2 — JSQ(d) is Lipschitz continuous with constant 2·d!·d²
-- statement:
--   Let $d\ge1$. For $x\in\mathcal X$ write $q_i=\sum_{j\ge i}x_j$, and let $p=(p_0,p_1,\dots)$ be the JSQ(d) assignment probability function (E.1),
--   $$p_{i-1}(x)=q_{i-1}^d-q_i^d\qquad(i=1,2,\dots).$$
--   Then for all $x,y\in\mathcal X$
--   $$\sum_{i=0}^\infty|p_i(x)-p_i(y)|\;\le\;2\,d!\,d^2\sum_{i=0}^\infty|x_i-y_i| .$$
--
--   This is the Lipschitz property (Definition 4.1) needed to apply the process-level limit theorem for Lipschitz policies to the JSQ(d) assignment function of the fully flexible system.
--
--   **Formalization Note** Both sides are computed in $[0,\infty]$ (`l1dist`). The tails $q_i$ are `tsum`s, which are the true tails on $\mathcal X$.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 16, Lemma 4.2; p. 41, App. E, (E.1)

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Policy

open Filter Topology
open scoped ENNReal

namespace StrictCompatLB.MeanField

/-- Lemma 4.2 (p. 16; proof App. E, p. 41). For every `d ≥ 1`, the JSQ(d) assignment probability
function (E.1) is Lipschitz continuous in the sense of (4.1) with constant `2 d! d²`. -/
theorem lemma_4_2 (d : ℕ) (hd : 1 ≤ d) :
    IsLipschitzPolicyWith (jsqdAssign d) (2 * (d.factorial : ℝ) * (d : ℝ) ^ 2) := by sorry

end StrictCompatLB.MeanField
