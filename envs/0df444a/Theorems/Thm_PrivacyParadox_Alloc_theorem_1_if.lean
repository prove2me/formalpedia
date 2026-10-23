-- Prove2me | Theorems.Thm_PrivacyParadox_Alloc_theorem_1_if
-- name    : PrivacyParadox.Alloc.theorem_1_if
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:48.300917+00:00
-- url     : https://prove2.me/theorems/bed3f720-8d44-430b-a214-ffd3b934d94d
-- title:
--   Theorem 1 (if), p. 9 — a non-increasing (decreasing) allocation with payment (15) is (strictly) truthful and induces θ*
-- statement:
--   Fix one group of agents satisfying the standing assumptions (costs in $\mathcal C=[c_{\min},c_{\max}]$, privacy costs $h(c)=cb$ with $0\le b<1$ and $g\le h$, $h-g$ strictly increasing, a continuous positive density $f$, and threshold $\hat c$ with $F(\hat c)=\bar\theta>0$). Let $A$ be an allocation rule with $0<A(c)\le1$ on $\mathcal C$, and let $P$ be the payment (15)–(16) built from $A$.
--
--   1. If $A$ is non-increasing on $\mathcal C$, then the menu $(A,P)$ is truthful and induces the participation rate $\bar\theta$:
--   $$\bar u(\tilde c\mid c)\le\bar u(c\mid c)\quad(c,\tilde c\in\mathcal C),\qquad \int_{c_{\min}}^{c_{\max}}\mathbf 1[d(c)=1]\,f(c)\,dc=F(\hat c).$$
--   2. If $A$ is strictly decreasing on $\mathcal C$, then $(A,P)$ is strictly truthful and induces $\bar\theta$.
--
--   This is the sufficiency half of the paper's Theorem 1: it lets the analyst replace the truthfulness constraint by a monotonicity constraint on $A$ and substitute the closed-form payment into the budget.
--
--   **Formalization Note** The statement is per group at the fixed profile $\theta^*$. No differentiability of $A$ is assumed (the paper's proof differentiates $A$); a monotone function on an interval is integrable, so the payment is well defined. Participation $d(c)=1$ is "some report gives utility at least $-g(c)$".
-- source:
--   Liao, Su, Ziani, Wierman, Huang, arXiv:2105.14262v1, p. 9, Theorem 1 ("if" direction); proof App. A, pp. 17–19

import Mathlib
import Definitions.Def_PrivacyParadox_Alloc_Model

namespace PrivacyParadox.Alloc

theorem theorem_1_if (G : GroupData) (hG : G.Standing) (A : ℝ → ℝ)
    (hA : ∀ c ∈ G.C, 0 < A c ∧ A c ≤ 1) :
    (AntitoneOn A G.C → G.Truthful A (G.pay A) ∧ G.Induces A (G.pay A)) ∧
      (StrictAntiOn A G.C → G.StrictTruthful A (G.pay A) ∧ G.Induces A (G.pay A)) := by sorry

end PrivacyParadox.Alloc
