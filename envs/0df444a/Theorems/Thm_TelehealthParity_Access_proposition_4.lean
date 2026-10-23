-- Prove2me | Theorems.Thm_TelehealthParity_Access_proposition_4
-- name    : TelehealthParity.Access.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:06.016464+00:00
-- url     : https://prove2.me/theorems/43794d80-1bb0-4315-bd32-e74df00fc933
-- title:
--   Proposition 4 — under pay parity $0<q^\dagger<q^*<1$; for $q\in(q^\dagger,q^*)$ revenue is maximized at $\theta^*$ and access at $\theta=0$
-- statement:
--   Fix parameters satisfying the standing assumptions with $R>0$; only $\theta$ and the duplicate-visit probability $q$ vary. There are thresholds $q^\dagger$ and $q^*$ with
--   $$0<q^\dagger<q^*<1$$
--   such that, for every admissible $q$:
--   1. if $q<q^*$, the provider's revenue under pay parity $F(R,\cdot)$ is maximized over $[0,1]$ at $\theta=\theta^*$, and if $q>q^*$ it is maximized at $\theta=0$;
--   2. if $q<q^\dagger$, the patient access rate $A$ is maximized over $[0,1]$ at $\theta=\theta^*$, and if $q>q^\dagger$ it is maximized at $\theta=0$;
--   3. if $q^\dagger<q<q^*$, the two objectives disagree strictly:
--   $$A(\theta^*)<A(0)\qquad\text{and}\qquad F(R,0)<F(R,\theta^*).$$
--
--   Under telehealth pay parity, for a moderate duplicate-visit probability the provider maximizes its revenue by committing capacity to telehealth, while patient access is maximized by an office-only practice: the provider does more work, and is paid for the duplicate visits, while seeing fewer patients.
--
--   **Formalization Note** Items 1–2 are Proposition 3, which defines $q^*$ and $q^\dagger$; without them the thresholds would be meaningless. The paper's premise "$q^\dagger>0$" is part of the conclusion here (Proposition 3 gives it). Item 3 states the misalignment strictly, which is what "maximized at θ = 0, but … maximized at θ = θ*" asserts. $R>0$ is added (the paper allows $R\ge0$): with $R=0$ the revenue vanishes identically and the strict comparison fails.
-- source:
--   Çakıcı and Mills, Telehealth in Acute Care: Pay Parity and Patient Access, SSRN working paper (version of August 19, 2024), p. 18, Proposition 4, with the thresholds of Proposition 3 (pp. 17–18); proof Appendix C, EC p. 8 (PDF 41)

import Mathlib
import Definitions.Def_TelehealthParity_Access_Setting

namespace TelehealthParity.Access

theorem proposition_4 (p : Params) (hp : p.Standing) (hR : 0 < p.R) :
    ∃ qdag qstar : ℝ, 0 < qdag ∧ qdag < qstar ∧ qstar < 1 ∧
      ∀ q : ℝ, Admissible p q →
        (q < qstar → IsMaxOn (revenue p q p.R) (Set.Icc 0 1) (thetaStar p q)) ∧
        (qstar < q → IsMaxOn (revenue p q p.R) (Set.Icc 0 1) 0) ∧
        (q < qdag → IsMaxOn (access p q) (Set.Icc 0 1) (thetaStar p q)) ∧
        (qdag < q → IsMaxOn (access p q) (Set.Icc 0 1) 0) ∧
        (qdag < q → q < qstar →
          access p q (thetaStar p q) < access p q 0 ∧
            revenue p q p.R 0 < revenue p q p.R (thetaStar p q)) := by sorry

end TelehealthParity.Access
