-- Prove2me | Theorems.Thm_SeqLoss_TreeRules_fixedFractionTree_isTreeRule
-- name    : SeqLoss.TreeRules.fixedFractionTree_isTreeRule
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:43.183983+00:00
-- url     : https://prove2.me/theorems/11bf44f1-e0e4-4eee-8305-4631d2b57281
-- title:
--   §5, p. 16 — each fixed-fraction rule φ^λ, λ ∈ [0, 1], is a rule on loss trees
-- statement:
--   Let $\lambda\in[0,1]$ and let $\varphi^\lambda$ be the fixed-fraction rule on trees (Definition 2): for a tree $T$ with root $r$ and a loss $\ell\ge 0$,
--   $$\varphi^\lambda_i(T,\ell)=\lambda\sum_{ij\in T}\ell(ij)+[i=r]\,(1-\lambda)L,\qquad L=\sum_{e\in T}\ell(e).$$
--   Then $\varphi^\lambda$ is a rule on loss trees: for every tree $T$ and loss $\ell$, the liabilities of the agents $i\in N(T)$ are non-negative and sum to $L$; $\varphi^\lambda$ is invariant to agent labels (for every bijection $\pi$ of $\mathbb N$ and every loss $\ell^\pi$ agreeing with $\ell$ on $T^\pi$, $\varphi^\lambda_i(T,\ell)=\varphi^\lambda_{\pi(i)}(T^\pi,\ell^\pi)$); and $\varphi^\lambda_i(T,a\ell)\to\varphi^\lambda_i(T,\ell)$ as $a\to 1$.
--
--   The paper introduces Definition 2 with the remark that the fixed-fraction rules "extend in a straightforward way" to trees. This statement makes the remark precise and is the first half of the "if" direction of Theorem 4.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 16, §5, sentence before Definition 2, and footnote 9

import Mathlib
import Definitions.Def_SeqLoss_TreeRules_Setting

namespace SeqLoss.TreeRules

theorem fixedFractionTree_isTreeRule (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    IsTreeRule (fixedFractionTree lam) := by sorry

end SeqLoss.TreeRules
