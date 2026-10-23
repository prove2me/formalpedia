-- Prove2me | Theorems.Thm_PrivacyParadox_Alloc_corollary_1
-- name    : PrivacyParadox.Alloc.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:46.566399+00:00
-- url     : https://prove2.me/theorems/b88235fb-a694-4bba-8604-c1045e544d62
-- title:
--   Corollary 1, p. 10 — under the mechanism of Theorem 1, an agent participates iff c ≤ ĉ_i
-- statement:
--   Under the standing assumptions of a group, let $A$ be non-increasing on $\mathcal C=[c_{\min},c_{\max}]$ with $0<A\le1$ there, and let $P$ be the payment (15)–(16) built from $A$. Then for every cost $c\in\mathcal C$,
--   $$d(c\mid\theta^*)=1\iff c\le\hat c ,$$
--   where $d(c\mid\theta^*)=1$ means that some report $\tilde c\in\mathcal C$ gives participation utility $\bar u(\tilde c\mid c)\ge-g(c)$.
--
--   The participation decisions therefore have a threshold structure: exactly the agents with cost at most $\hat c$ join, which is how the threshold $\hat c$ of (14) realizes the participation rate $\bar\theta=F(\hat c)$.
--
--   **Formalization Note** "The mechanism in Theorem 1" is read as its non-increasing case, which contains the strictly decreasing one.
-- source:
--   Liao, Su, Ziani, Wierman, Huang, arXiv:2105.14262v1, p. 10, Corollary 1

import Mathlib
import Definitions.Def_PrivacyParadox_Alloc_Model

namespace PrivacyParadox.Alloc

theorem corollary_1 (G : GroupData) (hG : G.Standing) (A : ℝ → ℝ)
    (hA : ∀ c ∈ G.C, 0 < A c ∧ A c ≤ 1) (hmono : AntitoneOn A G.C) :
    ∀ c ∈ G.C, (G.Joins A (G.pay A) c ↔ c ≤ G.chat) := by sorry

end PrivacyParadox.Alloc
