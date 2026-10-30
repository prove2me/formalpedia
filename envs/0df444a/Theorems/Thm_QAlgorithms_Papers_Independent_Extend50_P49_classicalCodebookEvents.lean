-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P49_classicalCodebookEvents
-- name    : QAlgorithms.Papers.Independent.Extend50.P49.classicalCodebookEvents
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:24:33.732103+00:00
-- url     : https://prove2.me/theorems/aca4e430-2e4c-4d5d-ba87-a9f7a30a82a3
-- title:
--   Classical random-codebook covering, miss, and collision bounds
-- statement:
--   Fix a finite classical broadcast channel $W$, a normalized auxiliary law $p_{UV}$, and a deterministic map $f$. Write $a=I_0^{\varepsilon_0}(U;Y)$, $b=I_0^{\varepsilon_0}(V;Z)$, and $c=I_\infty^{\varepsilon_\infty}(U;V)$ for the finite values on the computed law $p_{UV}W(\cdot,\cdot\mid f(U,V))$. Suppose $0<\varepsilon_0<1$, $0<\varepsilon_\infty\le1/4$, and $0<t\le1/37$. Choose source test sets $A_1\subseteq U\times Y$, $A_2\subseteq V\times Z$ with acceptance strictly greater than $1-\varepsilon_0$ and original product-marginal masses at most $2^{-a}$ and $2^{-b}$, respectively. For positive integer message counts $M_i$ put $R_i=\log_2M_i$, and choose positive integers $r_i$ satisfying, with $L=\log_2(1/t)$,
--   $$R_1+r_1\le a-4L-1,\quad R_2+r_2\le b-4L-1,\quad r_1,r_2\ge L,\quad r_1+r_2=\lceil c+3L\rceil.$$
--   Draw all $M_12^{r_1}$ row symbols independently from $p_U$ and all $M_22^{r_2}$ column symbols independently from $p_V$, mutually independently. Given them, retain each cell $(k,\ell)$ independently with probability $\min\{1,p_{UV}(U_k,V_\ell)/(2^cp_U(U_k)p_V(V_\ell))\}$. Null marginal rows have probability zero. For the first message rectangle select the lexicographically first retained cell whose two conditional local test-acceptance probabilities exceed $1-4\varepsilon_0$; use a fixed channel input if none exists.
--   Let $E_1$ mean no such cell exists. On its complement denote the selected indices by $(k^*,\ell^*)$. Let $E_{2,B}$ and $E_{2,C}$ mean the selected row/output or column/output fails its test. Let $E_{3,B}$ and $E_{3,C}$ mean some OTHER row index or column index passes the corresponding output test. These events include randomness of both the codebook and actual channel output. Then, with
--   $$A=2^{-r_1-r_2+c+2}+2^{-r_1+4}+2^{-r_2+4},\quad B=2^{2r_1+r_2+R_1-c-a},\quad C=2^{r_1+2r_2+R_2-c-b},$$
--   all the following bounds hold:
--   $$\begin{aligned}\Pr(E_1)&\le A\le36t,\\\Pr(E_{2,B}),\Pr(E_{2,C})&\le4\varepsilon_0,\\\Pr(E_{3,B})&\le B\le t/2,\\\Pr(E_{3,C})&\le C\le t/2.\end{aligned}$$
--   The events are computed from this construction; they are not arbitrary events postulated to satisfy the bounds. Their union yields the classical budget $37t+8\varepsilon_0$.
-- source:
--   One-shot Marton inner bound for classical-quantum broadcast channel, arXiv:1410.3248v5, PDF p. 13, Claim 1

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P49

open QAlgorithms MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Claim 1, PDF p.13, proof pp.13-14. Corrected printed -r1-r1 to -r1-r2,
as required by the derivation on p.13 and (31), p.9. The collision constants are
visually verified tildeEpsilon/2, not 2*tildeEpsilon. All five events are computed. -/
theorem classicalCodebookEvents {X U V Y Z : Type}
    [Fintype X] [Fintype U] [Fintype V] [Fintype Y] [Fintype Z]
    (D : ClassicalSetup X U V Y Z) :
    let cover := (2 : ℝ) ^ (-(D.r1 : ℝ) - D.r2 + D.c + 2) +
      (2 : ℝ) ^ (-(D.r1 : ℝ) + 4) + (2 : ℝ) ^ (-(D.r2 : ℝ) + 4)
    let collisionBob := (2 : ℝ) ^ (2 * (D.r1 : ℝ) + (D.r2 : ℝ) + Real.logb 2 (D.M1 : ℝ)) *
      (2 : ℝ) ^ (-D.c) * (2 : ℝ) ^ (-D.a)
    let collisionCharlie := (2 : ℝ) ^ ((D.r1 : ℝ) + 2 * D.r2 + Real.logb 2 (D.M2 : ℝ)) *
      (2 : ℝ) ^ (-D.c) * (2 : ℝ) ^ (-D.b)
    classicalEventProbability D .noPair ≤ cover ∧ cover ≤ 36 * D.tildeEpsilon ∧
    classicalEventProbability D .bobMiss ≤ 4 * D.epsilon0 ∧
    classicalEventProbability D .charlieMiss ≤ 4 * D.epsilon0 ∧
    classicalEventProbability D .bobCollision ≤ collisionBob ∧ collisionBob ≤ D.tildeEpsilon / 2 ∧
    classicalEventProbability D .charlieCollision ≤ collisionCharlie ∧
      collisionCharlie ≤ D.tildeEpsilon / 2 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P49

end
