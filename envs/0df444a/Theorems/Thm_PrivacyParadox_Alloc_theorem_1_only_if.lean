-- Prove2me | Theorems.Thm_PrivacyParadox_Alloc_theorem_1_only_if
-- name    : PrivacyParadox.Alloc.theorem_1_only_if
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:50.360223+00:00
-- url     : https://prove2.me/theorems/19fa095e-4171-4998-97a7-a3ea8208673c
-- title:
--   Theorem 1 (only if), p. 9 — a (strictly) truthful menu inducing θ* has non-increasing (decreasing) A and payment (15), when θ̄*_i < 1
-- statement:
--   Fix one group satisfying the standing assumptions, and assume in addition $\hat c<c_{\max}$, i.e. the desired participation rate satisfies $\bar\theta=F(\hat c)<1$. Let $A$ be an allocation rule with $0<A\le1$ on $\mathcal C=[c_{\min},c_{\max}]$ and $P$ an arbitrary payment rule.
--
--   1. If $(A,P)$ is truthful and induces $\bar\theta$, then $A$ is non-increasing on $\mathcal C$ and $P$ coincides on $\mathcal C$ with the payment (15)–(16) built from $A$.
--   2. If $(A,P)$ is strictly truthful and induces $\bar\theta$, then $A$ is strictly decreasing on $\mathcal C$ and $P$ coincides on $\mathcal C$ with the payment (15)–(16).
--
--   In formulas, the conclusion on the payment is
--   $$P(c)=c-h(c)+\frac{1}{A(c)}\Big((1-b)\int_c^{c_{\max}}A(z)\,dz+\tau\Big)\qquad(c\in\mathcal C).$$
--
--   This is the necessity half of Theorem 1: the payment (15) is the only one compatible with truthfulness and the desired equilibrium, so optimizing over $A$ alone loses nothing.
--
--   **Formalization Note** The hypothesis $\bar\theta<1$ is added. At $\hat c=c_{\max}$ every payment of the form (31) with a constant $v\ge\tau$ (not only $v=\tau$) makes all agents of the group join, so $\theta^*$ is still induced while $P$ differs from (15). No differentiability of $A$ is assumed (the paper's envelope argument differentiates).
-- source:
--   Liao, Su, Ziani, Wierman, Huang, arXiv:2105.14262v1, p. 9, Theorem 1 ("only if" direction); proof App. A, pp. 18–19, (29)–(33)

import Mathlib
import Definitions.Def_PrivacyParadox_Alloc_Model

namespace PrivacyParadox.Alloc

theorem theorem_1_only_if (G : GroupData) (hG : G.Standing) (hlt : G.chat < G.cmax)
    (A P : ℝ → ℝ) (hA : ∀ c ∈ G.C, 0 < A c ∧ A c ≤ 1) :
    (G.Truthful A P → G.Induces A P → AntitoneOn A G.C ∧ ∀ c ∈ G.C, P c = G.pay A c) ∧
      (G.StrictTruthful A P → G.Induces A P →
        StrictAntiOn A G.C ∧ ∀ c ∈ G.C, P c = G.pay A c) := by sorry

end PrivacyParadox.Alloc
