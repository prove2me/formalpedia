-- Prove2me | Theorems.Thm_SLQSolv_OpenNotClosed_eq_7_3
-- name    : SLQSolv.OpenNotClosed.eq_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:21:19.058981+00:00
-- url     : https://prove2.me/theorems/a4168d62-6de3-4fdd-b4f1-bf74fcbf386e
-- title:
--   (7.3), p. 2305 — in Example 7.1 the Riccati equation has the unique solution P ≡ 1, which violates the range condition (4.7)
-- statement:
--   Consider the data of Example 7.1 ($n=1$, $m=2$, $A=0$, $B=(1,1)$, $C=0$, $D=(1,-1)$, $G=1$, $Q=0$, $S=0$, $R=0$, $T=1$) and fix $t\in[0,1)$. Then:
--
--   1. for every scalar function $P$ the right-hand side of the Riccati equation (4.6) vanishes, so (4.6) reads
--   $$
--   \dot P=P^2(1,1)\begin{pmatrix}P&-P\\-P&P\end{pmatrix}^\dagger\begin{pmatrix}1\\1\end{pmatrix}=0,\qquad P(1)=1;
--   $$
--   2. every solution of (4.6) on $[t,1]$ equals $1$ on $[t,1]$, and $P\equiv1$ is a solution;
--   3. for $P\equiv 1$ and every $s$, $\mathcal R\big(B^\top P+D^\top PC+S\big)=\{(a,a)^\top:a\in\mathbb R\}$ and $\mathcal R\big(R+D^\top PD\big)=\{(a,-a)^\top:a\in\mathbb R\}$;
--   4. hence the range condition (4.7) fails and $P\equiv1$ is not a regular solution on $[t,1]$.
--
--   Combined with Theorem 4.3, this is why the problem of Example 7.1 is closed-loop solvable on no interval $[t,1]$.
--
--   **Formalization Note** The paper states the fact on $[0,1]$; it is stated here on every $[t,1]$ with $t<1$, the form in which it is combined with Theorem 4.3 on $[t,1]$. The pseudoinverse is the literal Moore–Penrose pseudoinverse.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Example 7.1, (7.3) and the two range identities after it, p. 2305

import Mathlib
import Definitions.Def_SLQSolv_OpenNotClosed_Examples

open MeasureTheory Set Filter Topology
open scoped NNReal Matrix

namespace SLQSolv.OpenNotClosed

/-- (7.3), p. 2305, on `[t, 1]` for every `t < 1`: for the data of Example 7.1 the right-hand side of
the Riccati equation (4.6) vanishes for every `P`, the equation has the unique solution `P ≡ 1`,
`ℛ(BᵀP + DᵀPC + S) = {(a, a)ᵀ}`, `ℛ(R + DᵀPD) = {(a, −a)ᵀ}`, and `P ≡ 1` is not regular. -/
theorem eq_7_3 {Ω : Type*} (t : ℝ≥0) (ht : t < 1) :
    (∀ (P : ℝ≥0 → Matrix (Fin 1) (Fin 1) ℝ) (s : ℝ≥0), riccatiRhs (ex71 (Ω := Ω)) P s = 0) ∧
    (∀ P, IsRiccatiSolOn (ex71 (Ω := Ω)) t P → ∀ s, t ≤ s → s ≤ 1 → P s = 1) ∧
    IsRiccatiSolOn (ex71 (Ω := Ω)) t (fun _ => 1) ∧
    (∀ s, LinearMap.range (Matrix.mulVecLin (gainK (ex71 (Ω := Ω)) (fun _ => 1) s))
      = Submodule.span ℝ {![1, 1]}) ∧
    (∀ s, LinearMap.range (Matrix.mulVecLin (sigmaR (ex71 (Ω := Ω)) (fun _ => 1) s))
      = Submodule.span ℝ {![1, -1]}) ∧
    ¬ IsRegularOn (ex71 (Ω := Ω)) t (fun _ => 1) := by sorry

end SLQSolv.OpenNotClosed
