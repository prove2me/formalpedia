-- Prove2me | Theorems.Thm_SLQSolv_MinSeq_theorem_6_1
-- name    : SLQSolv.MinSeq.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:20:38.574485+00:00
-- url     : https://prove2.me/theorems/70a536ee-35a0-4703-ad4a-2f67b5dc5ce9
-- title:
--   Theorem 6.1, pp. 2300–2301 — if (SLQ) is finite, the Riccati feedback controls u_ε of (6.2) form a minimizing sequence: J(t, x; u_ε) → V(t, x)
-- statement:
--   Assume (H1)–(H2) and that Problem (SLQ) is finite, i.e. $V(t,x)>-\infty$ for all $(t,x)\in[0,T]\times\mathbb R^n$. Fix $(t,x)\in[0,T)\times\mathbb R^n$. For every $\varepsilon>0$ let $P_\varepsilon$ be a strongly regular solution of the Riccati equation (5.7), i.e. (4.6) with $R$ replaced by $R+\varepsilon I$; let $(\eta_\varepsilon,\zeta_\varepsilon)$ be the adapted solution of the backward equation (4.11) for the same data and $P_\varepsilon$; put $\Theta_\varepsilon=-(R+\varepsilon I+D^\top P_\varepsilon D)^{-1}(B^\top P_\varepsilon+D^\top P_\varepsilon C+S)$ and $v_\varepsilon=-(R+\varepsilon I+D^\top P_\varepsilon D)^{-1}(B^\top\eta_\varepsilon+D^\top\zeta_\varepsilon+D^\top P_\varepsilon\sigma+\rho)$ as in (6.1); let $X_\varepsilon$ solve the closed-loop system $dX_\varepsilon=[(A+B\Theta_\varepsilon)X_\varepsilon+Bv_\varepsilon+b]ds+[(C+D\Theta_\varepsilon)X_\varepsilon+Dv_\varepsilon+\sigma]dW$ on $[t,T]$, $X_\varepsilon(t)=x$; and set $u_\varepsilon=\Theta_\varepsilon X_\varepsilon+v_\varepsilon$ as in (6.2). Then $(u_\varepsilon)$ is a minimizing sequence:
--
--   $$
--   \lim_{\varepsilon\to0^+}J(t,x;u_\varepsilon)=\inf_{u\in\mathcal U[t,T]}J(t,x;u)=V(t,x).
--   $$
--
--   This gives an explicit minimizing sequence for a finite problem with no convexity assumption beyond what finiteness implies; Theorem 6.2 characterizes open-loop solvability by its convergence.
--
--   **Formalization Note** The backward equation is (4.11) of p. 2285 for the data with $R+\varepsilon I$, whose $\rho$-term is $-(P_\varepsilon B+C^\top P_\varepsilon D+S^\top)(R+\varepsilon I+D^\top P_\varepsilon D)^{-1}\rho=+\Theta_\varepsilon^\top\rho$. Theorem 6.1 on p. 2300 prints $-\Theta_\varepsilon^\top\rho$; its proof invokes Corollary 4.7 (p. 2291), which uses (4.11), so the sign of (4.11) is the one formalized. A scalar example confirms (4.11). The families $P_\varepsilon,(\eta_\varepsilon,\zeta_\varepsilon),X_\varepsilon$ enter as hypotheses that pin them by their equations for every $\varepsilon>0$ (each is unique: the strongly regular Riccati solution by [23], the BSDE and the SDE by their uniqueness theorems), so $u_\varepsilon$ is the Riccati feedback sequence (6.2), not an arbitrary minimizing sequence. The sequence is written `uEps`. The limit is taken in the extended reals, $V$ being an extended-real infimum. (H1)–(H2) are the standing assumptions; the state, cost, value function and optimality notions are those of the shared `Setting` module.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Theorem 6.1, (6.1)–(6.3), pp. 2300–2301

import Mathlib
import Definitions.Def_SLQSolv_MinSeq_Sequence

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal Matrix

namespace SLQSolv.MinSeq

/-- Theorem 6.1, pp. 2300–2301: if Problem (SLQ) is finite, the Riccati feedback controls
`u_ε = Θ_ε X_ε + v_ε` of (6.2) form a minimizing sequence: `J(t, x; u_ε) → V(t, x)` as `ε → 0⁺`.
`P_ε` is the strongly regular solution of (5.7), `(η_ε, ζ_ε)` solves the BSDE (4.11) of the data with
`R + εI` (the page prints `−Θ_εᵀρ`; (4.11) gives `+Θ_εᵀρ`), `X_ε` the closed-loop system from `(t, x)`. -/
theorem theorem_6_1 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω) (d : Data Ω n m)
    (h1 : H1 Bs d) (h2 : H2 Bs d)
    (hfin : IsFinite Bs d) (t : ℝ≥0) (ht : t < d.T) (x : Fin n → ℝ)
    (Pε : ℝ → ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ ε > 0, IsStronglyRegular (d.addR ε) (Pε ε))
    (η ζ : ℝ → ℝ≥0 → Ω → Fin n → ℝ)
    (hηζ : ∀ ε > 0, IsAdjointEta Bs (d.addR ε) (Pε ε) (η ε) (ζ ε))
    (X : ℝ → ℝ≥0 → Ω → Fin n → ℝ)
    (hX : ∀ ε > 0, IsClosedLoopState Bs d t (thetaOf (d.addR ε) (Pε ε))
      (vOf (d.addR ε) (Pε ε) (η ε) (ζ ε)) x (X ε)) :
    Tendsto (fun ε => ((J Bs d t x (uEps d Pε η ζ X ε) : ℝ) : EReal)) (𝓝[>] 0)
      (𝓝 (V Bs d t x)) := by sorry

end SLQSolv.MinSeq
