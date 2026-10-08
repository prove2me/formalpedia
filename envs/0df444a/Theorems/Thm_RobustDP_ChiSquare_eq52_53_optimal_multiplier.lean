-- Prove2me | Theorems.Thm_RobustDP_ChiSquare_eq52_53_optimal_multiplier
-- name    : RobustDP.ChiSquare.eq52_53_optimal_multiplier
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:01.696037+00:00
-- url     : https://prove2.me/theorems/16f20f2d-d488-457c-af7f-b1780f4d43fd
-- title:
--   Proof of Lemma 5, eqs. (52)–(53) — an optimal multiplier has the form $\mu^*(s)=(v(s)-\alpha)^+$ with $\alpha\ge v_{\min}$
-- statement:
--   Let $\mathcal S$ be a finite set, $q\in\mathcal M(\mathcal S)$ with $q(s)>0$ for every $s$, $t\ge 0$ and $v:\mathcal S\to\mathbb R$, and let $g(\mu)=\mathbf E^q[v-\mu]-\sqrt{t\,\mathbf{Var}^q[v-\mu]}$ be the objective of the dual problem (48). There is a real number $\alpha$ with
--
--   $$
--   \alpha\ge v_{\min}=\min_{s\in\mathcal S}v(s)
--   $$
--
--   such that the multiplier
--
--   $$
--   \mu^*(s)=\begin{cases}v(s)-\alpha, & v(s)\ge\alpha,\\ 0, & \text{otherwise,}\end{cases}
--   $$
--
--   maximizes $g$ over all $\mu\ge 0$, i.e. $g(\mu^*)\ge g(\mu)$ for every $\mu:\mathcal S\to\mathbb R$ with $\mu\ge 0$.
--
--   Consequently the dual problem (48) reduces to a search over the single scalar $\alpha$; this is the basis of the sorting algorithm of the paper.
--
--   **Formalization Note** The bound $\alpha\ge v_{\min}$ is stated as "$v(s)\le\alpha$ for some $s$", which is equivalent on a finite nonempty set. The page derives the form of $\mu^*$ from complementary slackness and the characterization $v(s)-\mu(s)=\|z\|/\sqrt t+\mathbf E^q[v-\mu]=\alpha$ on $\{\mu>0\}$ (52); the latter divides by $\sqrt t$ and is not stated separately. The statement includes that the dual maximum is attained.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 19, proof of Lemma 5, eqs. (52)–(53)

import Mathlib
import Definitions.Def_RobustDP_ChiSquare_Moments
import Definitions.Def_RobustDP_ChiSquare_ChiSqSet

namespace RobustDP.ChiSquare

/-- Proof of Lemma 5, eqs. (52)–(53) (Iyengar, TR-2002-07, p. 19): the dual problem (48) has an
optimal multiplier of the form `μ*(s) = v(s) − α` if `v(s) ≥ α` and `0` otherwise, for some
`α ≥ v_min = min_s v(s)`; so (48) reduces to a search over the scalar `α`. -/
theorem eq52_53_optimal_multiplier {S : Type*} [Fintype S] (q : S → ℝ)
    (hq : q ∈ stdSimplex ℝ S) (hq_pos : ∀ s, 0 < q s) (t : ℝ) (ht : 0 ≤ t) (v : S → ℝ) :
    ∃ α : ℝ, (∃ s, v s ≤ α) ∧
      IsGreatest ((fun μ => dualObj q t v μ) '' {μ : S → ℝ | 0 ≤ μ})
        (dualObj q t v (fun s => if α ≤ v s then v s - α else 0)) := by sorry

end RobustDP.ChiSquare
