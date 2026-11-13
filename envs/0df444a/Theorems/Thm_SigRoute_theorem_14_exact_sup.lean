-- Prove2me | Theorems.Thm_SigRoute_theorem_14_exact_sup
-- name    : SigRoute.theorem_14_exact_sup
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:43:28.398616+00:00
-- url     : https://prove2.me/theorems/4ddb7aa2-4877-4ecb-939f-cce1db69fc30
-- title:
--   Theorem 14, 'In particular' — exact supremum $\Lambda_{\mathcal Q_\gamma}(\lambda)=1+\eta_B(\lambda)+\gamma(\eta_A(\lambda)-\eta_B(\lambda))^+$ (the remaining clauses are the goal)
-- statement:
--   Let $u_A,u_B>0$, $\varepsilon_A,\varepsilon_B\in[0,1]$, $\gamma\in[0,1]$ and $\lambda>0$, and put $\eta_X(\lambda)=\varepsilon_X(e^{\lambda u_X}-1)$. Then
--
--   $$
--   \Lambda_{\mathcal Q_\gamma}(\lambda)=1+\eta_B(\lambda)+\gamma\bigl(\eta_A(\lambda)-\eta_B(\lambda)\bigr)^+ .
--   $$
--
--   This is an equality: the formula is the exact supremum, and the sign of $\eta_A-\eta_B$ need not be that of $\varepsilon_A-\varepsilon_B$ when $u_A\ne u_B$. It is the second sentence of Theorem 14; the probability bounds are the other clauses of the goal `SigRoute.theorem_14`.
--
--   Differences from the source:
--   - reading: $\mathcal Q_\gamma$ printed without the constraint $(q_A,q_B)\in[0,1]^2$ → $\mathcal Q_\gamma\cap[0,1]^2$ (`Qgamma`); reason: Definition 12 requires a soundness profile to be a subset of $[0,1]^2$; the intersection does not change the supremum in Theorem 14
--   - encoding: soundness errors $\varepsilon_A,\varepsilon_B$ and forgery rate $\gamma$, which are probabilities (§2, p.4; "trivially $\gamma\le1$", p.7) → explicit hypotheses $\varepsilon_A,\varepsilon_B,\gamma\in[0,1]$ in the exact-supremum statement; reason: the source's quantities always satisfy them; they make the corners $(g\varepsilon_A,(1-g)\varepsilon_B)$, $g\in[0,\gamma]$, lie in $[0,1]^2$, so the intersection with $[0,1]^2$ does not change the supremum
-- source:
--   Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Theorem 14, second sentence ("In particular"), p.7

import Mathlib
import Definitions.Def_SigRoute_IsProfile
import Definitions.Def_SigRoute_Qgamma

namespace SigRoute

/-- Theorem 14, second sentence ("In particular", exact supremum) (Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Theorem 14, p.7): with
`Q = Q_γ` and `η_X(λ) = ε_X(e^{λu_X} − 1)`, `Λ_{Q_γ}(λ) = 1 + η_B(λ) + γ(η_A(λ) − η_B(λ))⁺`, the exact
supremum. The remaining clauses of Theorem 14 are the goal `theorem_14`.

**Formalization Note** `ε_A, ε_B, γ ∈ [0, 1]` (soundness errors and the forgery rate are probabilities;
p.7: "trivially γ ≤ 1"); `Q_γ` is intersected with `[0,1]²` (`Qgamma`). Credits are any
`u_A, u_B > 0`. -/
theorem theorem_14_exact_sup (u : Arm → ℝ) (hu : ∀ X, 0 < u X) (ε : Arm → ℝ)
    (hε : ∀ X, ε X ∈ Set.Icc (0 : ℝ) 1) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (lam : ℝ) (hlam : 0 < lam) :
    Lam u (Qgamma ε γ) lam
      = 1 + eta ε u lam Arm.B + γ * max (eta ε u lam Arm.A - eta ε u lam Arm.B) 0 := by sorry

end SigRoute
