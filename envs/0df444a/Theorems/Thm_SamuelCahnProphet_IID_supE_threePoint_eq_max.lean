-- Prove2me | Theorems.Thm_SamuelCahnProphet_IID_supE_threePoint_eq_max
-- name    : SamuelCahnProphet.IID.supE_threePoint_eq_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:21:50.502719+00:00
-- url     : https://prove2.me/theorems/0641366b-e5b7-4077-9ce1-ce0db6d00687
-- title:
--   Proof of Theorem 2, p. 1215 — only two competing rules in T*ₙ, viz. t(a) and t(1)
-- statement:
--   Fix reals $0 < a < 1$, $b > 0$, $c > 0$ and an integer $n \ge 1$ with $b + c < n$. Let $X_1, \dots, X_n$ be i.i.d., taking the values $0$, $a$ and $1$ with probabilities $1 - (b+c)/n$, $c/n$ and $b/n$. Then the best threshold rule in $T_n^*$ is $t(a)$ or $t(1)$:
--   $$
--   \sup_{t \in T_n^*} EX_t = \max\{EX_{t(a)},\ EX_{t(1)}\}.
--   $$
--
--   The paper states that "there are essentially only two competing rules in $T_n^*$, viz. $t(a)$ and $t(1)$"; the identity above is that claim. It reduces the gambler's side of the extremal example to two explicit expectations.
--
--   **Formalization Note.** $T_n^*$ consists of $t(c)$ and $s(c)$ for all $c \ge 0$, both families included. The hypothesis $b + c < n$ is the page's, and makes the law a probability measure.
-- source:
--   Samuel-Cahn, Comparison of threshold stop rules and maximum for independent nonnegative random variables, Ann. Probab. 12 (1984), p. 1215, proof of Theorem 2 ("There are essentially only two competing rules in T*ₙ, viz. t(a) and t(1).")

import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting

open MeasureTheory Filter Topology

namespace SamuelCahnProphet.IID

theorem supE_threePoint_eq_max (a b c : ℝ) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b)
    (hc : 0 < c) (n : ℕ) [NeZero n] (hn : b + c < n) :
    supE (threePoint n a b c) n =
      max (EstopT (threePoint n a b c) n a) (EstopT (threePoint n a b c) n 1) := by sorry

end SamuelCahnProphet.IID
