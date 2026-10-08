-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Sensitive_Dinf_nonempty
-- name    : VeinottSensitiveDP.Sensitive.Dinf_nonempty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:25.163168+00:00
-- url     : https://prove2.me/theorems/801847c9-61f2-408e-94f3-1233940b1fea
-- title:
--   §4, p. 1646 — D_∞^+ is nonempty, and D_∞^− is nonempty in the transient case
-- statement:
--   In the model of §4 (every $P(f)$ substochastic), there is a decision rule $f$ whose stationary policy $f^\infty$ is $\infty^+$ discount optimal: for some $\rho^*>0$,
--   $$V_\rho(f^\infty)\ge V_\rho(\pi)\qquad\text{for all policies }\pi\text{ and }0<\rho<\rho^*.$$
--   In the transient case (every stationary policy transient) there is likewise an $f$ with $V_\rho(f^\infty)\ge V_\rho(\pi)$ for all $\pi$ and $-\rho^*<\rho<0$.
--
--   This generalizes Blackwell's existence of a stationary policy that is optimal for all discount factors near one, and it is what makes every $D_n^\pm$ nonempty.
--
--   **Formalization Note** The two signs $\pm$ are one real parameter $\sigma\in\{1,-1\}$: $\sigma=1$ is $+$ and $\sigma=-1$ is $-$. The comparison is with all policies, not only stationary ones.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1646, §4 ("Essentially the same proofs show that D_∞^+(D_∞^−) is nonempty where P(f) is substochastic (transient) for each f ε F")

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Matrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Model
import Definitions.Def_VeinottSensitiveDP_Sensitive_Optimality
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottSensitiveDP.Sensitive

/-- `D_∞^+` is nonempty (when every `P(f)` is substochastic), and `D_∞^−` is nonempty in the
transient case: some stationary policy `f^∞` satisfies, for some `ρ* > 0`,
`V_ρ(f^∞) ≧ V_ρ(π)` for all policies `π` and `0 < ±ρ < ρ*`.

Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1646, §4 ("Essentially the same proofs show that D_∞^+(D_∞^−) is nonempty where P(f) is
substochastic (transient) for each f ε F").

**Formalization Note.** `σ = 1` is the sign `+` and `σ = −1` the sign `−`. The model's standing assumption is that every `P(f)` is
substochastic; the `−` case adds the transient case (every stationary policy transient). The
comparison is with **all** policies `ℕ → F`. -/
theorem Dinf_nonempty {St : Type} [Fintype St] [DecidableEq St] [Nonempty St]
    {A : St → Type} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]
    (M : Model St A)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (htr : σ = -1 → M.TransientCase) :
    (M.Dinf σ).Nonempty := by sorry

end VeinottSensitiveDP.Sensitive
