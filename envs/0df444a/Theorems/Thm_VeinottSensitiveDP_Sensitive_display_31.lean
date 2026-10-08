-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Sensitive_display_31
-- name    : VeinottSensitiveDP.Sensitive.display_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:23.34704+00:00
-- url     : https://prove2.me/theorems/01383d62-9968-4405-9c22-0eede26b3340
-- title:
--   (30)–(31) — v_ρ(g, π) = (1 + ρ)[V_ρ(g, π) − V_ρ(π)] and V_ρ(g^∞) − V_ρ(π) = R_ρ(Q(g))v_ρ(g, π)
-- statement:
--   In the model of §4, let $\rho>-1$, $\beta=(1+\rho)^{-1}$, and suppose $|\sigma(\beta P(f))|<1$ for all $f\in F$. For $g\in F$ and every policy $\pi$, with $v_\rho(g,\pi)=r(g)+Q(g)V_\rho(\pi)-\rho V_\rho(\pi)$,
--   $$v_\rho(g,\pi)=(1+\rho)\,[V_\rho(g,\pi)-V_\rho(\pi)] \tag{30}$$
--   and
--   $$V_\rho(g^\infty)-V_\rho(\pi)=R_\rho(Q(g))\,v_\rho(g,\pi). \tag{31}$$
--
--   (31) reduces the comparison of the stationary policy $g^\infty$ with an arbitrary policy to the sign of the one-step test quantity $v_\rho(g,\pi)$, which is the basis of the policy improvement method.
--
--   **Formalization Note** $(g,\pi)$ is the policy that uses $g$ first and then follows $\pi$. The paper obtains (31) from Lemma 1 of §2; it is restated here for the discounted program.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1647, §4, (30), (31)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Matrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Model
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottSensitiveDP.Sensitive

/-- (30)–(31): suppose `−1 < ρ`, `β = (1 + ρ)⁻¹` and `|σ(βP(f))| < 1` for all `f ε F`. Then for
every `g ε F` and every policy `π`,
(30) `v_ρ(g, π) ≡ r(g) + Q(g)V_ρ(π) − ρV_ρ(π) = (1 + ρ)[V_ρ(g, π) − V_ρ(π)]`, and
(31) `V_ρ(g^∞) − V_ρ(π) = R_ρ(Q(g))v_ρ(g, π)`.

Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1647, §4, (30), (31).

**Formalization Note.** `v_ρ` is defined by the first expression of (30) (`Model.vrho`); the second
equality of (30) is the first conjunct. The paper derives (31) from Lemma 1 of §2 (formalized in
the companion mission on §2); it is restated here for the discounted program because a draft
cannot import another draft. `R_ρ(Q(g))` is `resolvent ρ (M.Q g)`. The hypothesis on every
`f` is what makes `V_ρ(π)` a convergent series for every policy `π` (Corollary 4 of §2 applied to
`βP(·)`). -/
theorem display_31 {St : Type} [Fintype St] [DecidableEq St] [Nonempty St]
    {A : St → Type} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]
    (M : Model St A)
    (ρ : ℝ) (hρ : -1 < ρ) (hall : ∀ f : DecisionRule A, VeinottSensitiveDP.Transient.specRad (beta ρ • M.P f) < 1)
    (g : DecisionRule A) (π : Policy A) :
    M.vrho ρ g π = (1 + ρ) • (M.V ρ (cons g π) - M.V ρ π) ∧
      M.V ρ (stationary g) - M.V ρ π = resolvent ρ (M.Q g) *ᵥ M.vrho ρ g π := by sorry

end VeinottSensitiveDP.Sensitive
