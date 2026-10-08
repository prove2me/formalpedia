-- Prove2me | Theorems.Thm_SethiChengSS_Infinite_w_claim
-- name    : SethiChengSS.Infinite.w_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:33.546678+00:00
-- url     : https://prove2.me/theorems/eefff502-5352-4f82-a981-8bb4b3c8cecc
-- title:
--   p. 937, after (6.6) — the order-nothing cost w_n is finite, lies in C_1 and is the unique C_1 solution of (6.7)
-- statement:
--   Consider the Markov-modulated inventory model under the standing assumptions (2.1)–(2.2), with discount factor $0 < \alpha < 1$. Let
--   $$w_n(i,x) = J_n(i,x;\mathbf 0)$$
--   be the expected discounted cost from period $n$, state $i$ and surplus $x$ when nothing is ever ordered (6.6). Then:
--
--   1. $w_n(i,x) < \infty$ for every $n$, $i$, $x$;
--   2. the functions $w_n$ lie in $C_1$, with one growth constant $C'$ for all $n$: $w_n(i,x) \le C'(1+|x|)$;
--   3. they solve
--   $$w_n(i,x) = f_n(i,x) + \alpha\,F_{n+1}(w_{n+1})(i,x), \qquad n = 0,1,2,\dots; \tag{6.7}$$
--   4. any sequence $b_n$ in $C_1$ (with one growth constant for all $n$) solving (6.7) coincides with $w_n$.
--
--   The function $w_n$ is the upper bound that makes the successive approximations $v_{n,k}$ of the infinite-horizon value converge (6.8).
--
--   **Formalization Note.** The paper prints $0 < \alpha \le 1$ (p. 936); at $\alpha = 1$ the cost $w_n$ is infinite whenever $f \not\equiv 0$, so $\alpha < 1$ is assumed. "In class $C_1$" for the sequence $(w_n)$ is read with one growth constant for all periods; without it the uniqueness claim fails, because $w_n + \alpha^{-n}$ is also a $C_1$ solution of (6.7) for each $n$.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 937, (6.6)–(6.7) and the claim between them

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Infinite_Model

namespace SethiChengSS.Infinite

theorem w_claim {L : ℕ} (D : Model L) (α : ℝ) (hD : Standing D) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ n i x, w D α n i x < ⊤) ∧
    SeqInC1 (fun n i x => (w D α n i x).toReal) ∧
    BellmanW D α (fun n i x => (w D α n i x).toReal) ∧
    ∀ b : ℕ → Fin L → ℝ → ℝ, SeqInC1 b → BellmanW D α b →
      ∀ n i x, b n i x = (w D α n i x).toReal := by sorry

end SethiChengSS.Infinite
