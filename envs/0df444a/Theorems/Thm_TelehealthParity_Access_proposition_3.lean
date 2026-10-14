-- Prove2me | Theorems.Thm_TelehealthParity_Access_proposition_3
-- name    : TelehealthParity.Access.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:15.101663+00:00
-- url     : https://prove2.me/theorems/6bfd9206-a1f6-478d-88e1-8cdc46b17247
-- title:
--   Proposition 3, pp. 17–18 — duplicate-visit thresholds $q^*$ (revenue under pay parity) and $q^\dagger$ (access)
-- statement:
--   Fix parameters satisfying the standing assumptions; only $\theta$ and the duplicate-visit probability $q$ vary.
--
--   1. **Revenue under pay parity** ($r=R$). There is a threshold $q^*\in(0,1)$ such that for every admissible $q$: if $q<q^*$, then $F(R,\cdot)$ is maximized over $[0,1]$ at $\theta=\theta^*$; if $q>q^*$, it is maximized at $\theta=0$.
--   2. **Access.** There is a threshold $q^\dagger\in(0,1)$ such that for every admissible $q$: if $q<q^\dagger$, then $A$ is maximized over $[0,1]$ at $\theta=\theta^*$; if $q>q^\dagger$, it is maximized at $\theta=0$.
--
--   In symbols, with $\theta^*=\theta^*(q)$ from (24),
--   $$q<q^*\Rightarrow F(R,\theta)\le F(R,\theta^*)\ \forall\theta\in[0,1],\qquad q>q^*\Rightarrow F(R,\theta)\le F(R,0)\ \forall\theta\in[0,1],$$
--   and likewise for $A$ with $q^\dagger$.
--
--   Under pay parity the provider offers telehealth exactly when duplicate visits are rare enough, and telehealth improves patient access exactly when they are rare enough; the two thresholds are compared in Proposition 4.
--
--   **Formalization Note** "Fix all problem parameters other than θ and q" is rendered by the quantifier order: each threshold is chosen once, before the universally quantified $q$. The thresholds need not be admissible values of $q$ themselves.
-- source:
--   Çakıcı and Mills, Telehealth in Acute Care: Pay Parity and Patient Access, SSRN working paper (version of August 19, 2024), pp. 17–18, Proposition 3; proof Appendix C, EC p. 8 (PDF 41)

import Mathlib
import Definitions.Def_TelehealthParity_Access_Setting

namespace TelehealthParity.Access

theorem proposition_3 (p : Params) (hp : p.Standing) :
    (∃ qstar : ℝ, 0 < qstar ∧ qstar < 1 ∧
      ∀ q : ℝ, Admissible p q →
        (q < qstar → IsMaxOn (revenue p q p.R) (Set.Icc 0 1) (thetaStar p q)) ∧
        (qstar < q → IsMaxOn (revenue p q p.R) (Set.Icc 0 1) 0)) ∧
    (∃ qdag : ℝ, 0 < qdag ∧ qdag < 1 ∧
      ∀ q : ℝ, Admissible p q →
        (q < qdag → IsMaxOn (access p q) (Set.Icc 0 1) (thetaStar p q)) ∧
        (qdag < q → IsMaxOn (access p q) (Set.Icc 0 1) 0)) := by sorry

end TelehealthParity.Access
