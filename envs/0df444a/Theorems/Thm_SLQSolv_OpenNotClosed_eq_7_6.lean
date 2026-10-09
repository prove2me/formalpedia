-- Prove2me | Theorems.Thm_SLQSolv_OpenNotClosed_eq_7_6
-- name    : SLQSolv.OpenNotClosed.eq_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:21:26.754442+00:00
-- url     : https://prove2.me/theorems/a7dda75b-8a57-4fd0-9734-2119497f968d
-- title:
--   (7.5)–(7.6), p. 2305 — the regularized Riccati equation Ṗ_ε = (2/ε)P_ε² has the strongly regular solution P_ε(t) = ε/(ε + 2 − 2t)
-- statement:
--   Let $\varepsilon>0$ and consider the problem of Example 7.1 with the cost (7.4), $J^0_\varepsilon(t,x;u)=\mathbb E\big[X(1)^2+\varepsilon\int_t^1|u(s)|^2ds\big]$, i.e. with $R$ replaced by $R+\varepsilon I$. Then:
--
--   1. for every scalar function $P$ the Riccati equation (4.6) of this problem reads (7.5),
--   $$
--   \dot P_\varepsilon=P_\varepsilon^2(1,1)\begin{pmatrix}\varepsilon+P_\varepsilon&-P_\varepsilon\\-P_\varepsilon&\varepsilon+P_\varepsilon\end{pmatrix}^{-1}\begin{pmatrix}1\\1\end{pmatrix}=\frac2\varepsilon P_\varepsilon^2,\qquad P_\varepsilon(1)=1;
--   $$
--   2. the function (7.6)
--   $$
--   P_\varepsilon(t)=\frac{\varepsilon}{\varepsilon+2-2t},\qquad t\in[0,1],
--   $$
--   is a strongly regular solution of (4.6) on $[0,1]$;
--   3. it is the only solution on $[0,1]$.
--
--   These are the regularized Riccati solutions whose limit (7.7) gives the value function of Example 7.1.
--
--   **Formalization Note** The right-hand side is computed with the Moore–Penrose pseudoinverse, which equals the inverse printed in (7.5) since $(1,1)^\top$ is an eigenvector of $\varepsilon I+P\begin{pmatrix}1&-1\\-1&1\end{pmatrix}$ with eigenvalue $\varepsilon$. Strong regularity is stated as in (4.10), with some $\lambda>0$.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Example 7.1, (7.4)–(7.6), p. 2305

import Mathlib
import Definitions.Def_SLQSolv_OpenNotClosed_Examples

open MeasureTheory Set Filter Topology
open scoped NNReal Matrix

namespace SLQSolv.OpenNotClosed

/-- (7.5)–(7.6), p. 2305: for `ε > 0` the Riccati equation of Example 7.1 with `R` replaced by
`R + εI` (the cost (7.4)) reads `Ṗ_ε = (2/ε)P_ε²`, `P_ε(1) = 1`; its unique solution on `[0, 1]` is
`P_ε(t) = ε/(ε + 2 − 2t)`, and this solution is strongly regular. -/
theorem eq_7_6 {Ω : Type*} (ε : ℝ) (hε : 0 < ε) :
    let Pε : ℝ≥0 → Matrix (Fin 1) (Fin 1) ℝ := fun s => !![ε / (ε + 2 - 2 * (s : ℝ))]
    (∀ (P : ℝ≥0 → Matrix (Fin 1) (Fin 1) ℝ) (s : ℝ≥0),
      riccatiRhs ((ex71 (Ω := Ω)).addR ε) P s = !![-((2 / ε) * P s 0 0 ^ 2)]) ∧
    IsStronglyRegular ((ex71 (Ω := Ω)).addR ε) Pε ∧
    ∀ P, IsRiccatiSol ((ex71 (Ω := Ω)).addR ε) P → ∀ s, s ≤ 1 → P s = Pε s := by sorry

end SLQSolv.OpenNotClosed
