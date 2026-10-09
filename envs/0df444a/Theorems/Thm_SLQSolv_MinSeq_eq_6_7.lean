-- Prove2me | Theorems.Thm_SLQSolv_MinSeq_eq_6_7
-- name    : SLQSolv.MinSeq.eq_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:21:08.625427+00:00
-- url     : https://prove2.me/theorems/f6f2b0f8-d381-4579-b2da-64edf0dcc5fc
-- title:
--   (6.7), p. 2302 — ε E∫|u_ε|² ⩽ V_ε(t, x) − V(t, x) ⩽ ε E∫|v*|² for any open-loop optimal v*
-- statement:
--   Assume (H1)–(H2) and that $u\mapsto J^0(0,0;u)$ is convex. Fix $(t,x)\in[0,T)\times\mathbb R^n$. For every $\varepsilon>0$ let $P_\varepsilon$ be a strongly regular solution of the Riccati equation (5.7), i.e. (4.6) with $R$ replaced by $R+\varepsilon I$; let $(\eta_\varepsilon,\zeta_\varepsilon)$ be the adapted solution of the backward equation (4.11) for the same data and $P_\varepsilon$; put $\Theta_\varepsilon=-(R+\varepsilon I+D^\top P_\varepsilon D)^{-1}(B^\top P_\varepsilon+D^\top P_\varepsilon C+S)$ and $v_\varepsilon=-(R+\varepsilon I+D^\top P_\varepsilon D)^{-1}(B^\top\eta_\varepsilon+D^\top\zeta_\varepsilon+D^\top P_\varepsilon\sigma+\rho)$ as in (6.1); let $X_\varepsilon$ solve the closed-loop system $dX_\varepsilon=[(A+B\Theta_\varepsilon)X_\varepsilon+Bv_\varepsilon+b]ds+[(C+D\Theta_\varepsilon)X_\varepsilon+Dv_\varepsilon+\sigma]dW$ on $[t,T]$, $X_\varepsilon(t)=x$; and set $u_\varepsilon=\Theta_\varepsilon X_\varepsilon+v_\varepsilon$ as in (6.2). Let $V_\varepsilon$ be the value function of Problem (SLQ)$_\varepsilon$, whose cost (6.4) is $J_\varepsilon(t,x;u)=J(t,x;u)+\varepsilon\mathbb E\int_t^T|u|^2ds$. If $v^*$ is an open-loop optimal control of Problem (SLQ) at $(t,x)$, then for every $\varepsilon>0$
--
--   $$
--   \mathbb E\int_t^T|u_\varepsilon(s)|^2ds\le\frac{V_\varepsilon(t,x)-V(t,x)}{\varepsilon}\le\mathbb E\int_t^T|v^*(s)|^2ds.
--   $$
--
--   Thus open-loop solvability bounds the sequence $u_\varepsilon$ in $\mathcal U[t,T]$, the starting point of (i) ⇒ (ii) in Theorem 6.2.
--
--   **Formalization Note** The inequalities are stated multiplied by $\varepsilon>0$, in the extended reals (both value functions are finite here because $v^*$ is optimal). $J_\varepsilon$ and $V_\varepsilon$ are the cost and value of the data with $R$ replaced by $R+\varepsilon I$, since $\langle(R+\varepsilon I)u,u\rangle=\langle Ru,u\rangle+\varepsilon|u|^2$. The backward equation is (4.11) of p. 2285 for the data with $R+\varepsilon I$, whose $\rho$-term is $-(P_\varepsilon B+C^\top P_\varepsilon D+S^\top)(R+\varepsilon I+D^\top P_\varepsilon D)^{-1}\rho=+\Theta_\varepsilon^\top\rho$. Theorem 6.1 on p. 2300 prints $-\Theta_\varepsilon^\top\rho$; its proof invokes Corollary 4.7 (p. 2291), which uses (4.11), so the sign of (4.11) is the one formalized. A scalar example confirms (4.11). The families $P_\varepsilon,(\eta_\varepsilon,\zeta_\varepsilon),X_\varepsilon$ enter as hypotheses that pin them by their equations for every $\varepsilon>0$ (each is unique: the strongly regular Riccati solution by [23], the BSDE and the SDE by their uniqueness theorems), so $u_\varepsilon$ is the Riccati feedback sequence (6.2), not an arbitrary minimizing sequence. The sequence is written `uEps`. (H1)–(H2) are the standing assumptions; the state, cost, value function and optimality notions are those of the shared `Setting` module.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), §6, proof of Theorem 6.2, (6.4)–(6.7), pp. 2301–2302

import Mathlib
import Definitions.Def_SLQSolv_MinSeq_Sequence

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal Matrix

namespace SLQSolv.MinSeq

/-- (6.7), §6, proof of Theorem 6.2, p. 2302: under convexity of `u ↦ J⁰(0, 0; u)`, if `v*` is an
open-loop optimal control at `(t, x)` then, for every `ε > 0`,
`E∫ₜᵀ|u_ε|² ≤ (V_ε(t, x) − V(t, x))/ε ≤ E∫ₜᵀ|v*|²`, written multiplied by `ε > 0`, with
`V_ε` the value function of the data with `R + εI` (cost (6.4)). -/
theorem eq_6_7 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω) (d : Data Ω n m)
    (h1 : H1 Bs d) (h2 : H2 Bs d)
    (hconv : IsConvexJ0 Bs d) (t : ℝ≥0) (ht : t < d.T) (x : Fin n → ℝ)
    (Pε : ℝ → ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ ε > 0, IsStronglyRegular (d.addR ε) (Pε ε))
    (η ζ : ℝ → ℝ≥0 → Ω → Fin n → ℝ)
    (hηζ : ∀ ε > 0, IsAdjointEta Bs (d.addR ε) (Pε ε) (η ε) (ζ ε))
    (X : ℝ → ℝ≥0 → Ω → Fin n → ℝ)
    (hX : ∀ ε > 0, IsClosedLoopState Bs d t (thetaOf (d.addR ε) (Pε ε))
      (vOf (d.addR ε) (Pε ε) (η ε) (ζ ε)) x (X ε))
    (vstar : ℝ≥0 → Ω → Fin m → ℝ) (hv : IsOpenLoopOptimal Bs d t x vstar) :
    ∀ ε > 0,
      (((ε * sqNorm Bs d t (uEps d Pε η ζ X ε) : ℝ) : EReal)
          ≤ V Bs (d.addR ε) t x - V Bs d t x) ∧
        V Bs (d.addR ε) t x - V Bs d t x ≤ (((ε * sqNorm Bs d t vstar : ℝ)) : EReal) := by sorry

end SLQSolv.MinSeq
