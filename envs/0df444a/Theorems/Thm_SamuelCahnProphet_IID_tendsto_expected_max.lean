-- Prove2me | Theorems.Thm_SamuelCahnProphet_IID_tendsto_expected_max
-- name    : SamuelCahnProphet.IID.tendsto_expected_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:21:35.151769+00:00
-- url     : https://prove2.me/theorems/09665f72-149a-41ed-bc4a-5f5eb04cb70c
-- title:
--   Proof of Theorem 2, p. 1215 — E = lim EXₙ⁽ⁿ⁾* = 1 − e^{−b} + a{e^{−b} − e^{−b−c}}
-- statement:
--   Fix reals $0 < a < 1$, $b > 0$, $c > 0$. For each $n$ let $X_1^{(n)}, \dots, X_n^{(n)}$ be i.i.d., taking the values $0$, $a$ and $1$ with probabilities $1 - (b+c)/n$, $c/n$ and $b/n$ respectively. Then
--   $$
--   E = \lim_{n \to \infty} E X_n^{(n)*} = 1 - e^{-b} + a\{e^{-b} - e^{-b-c}\},
--   $$
--   where $X_n^{(n)*} = \max(X_1^{(n)}, \dots, X_n^{(n)})$.
--
--   This is the limit of the prophet's value along the extremal family used to show that the constant 2 of Theorem 2 cannot be lowered.
--
--   **Formalization Note.** The sequence is indexed by $n = k + 1$, $k \in \mathbb N$. The law is a probability measure only once $n \ge b + c$; the finitely many earlier terms (where the Lean weights are clipped at $0$) do not affect the limit. The expectation is computed in $[0, \infty]$ and converted to a real number with `toReal`; it is at most $1$ once $n \ge b + c$.
-- source:
--   Samuel-Cahn, Comparison of threshold stop rules and maximum for independent nonnegative random variables, Ann. Probab. 12 (1984), p. 1215, proof of Theorem 2, display "E = lim EXₙ⁽ⁿ⁾*"

import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting

open MeasureTheory Filter Topology

namespace SamuelCahnProphet.IID

theorem tendsto_expected_max (a b c : ℝ) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b)
    (hc : 0 < c) :
    Tendsto (fun k : ℕ => (Emax (threePoint ((k + 1 : ℕ) : ℝ) a b c) (k + 1)).toReal) atTop
      (𝓝 (1 - Real.exp (-b) + a * (Real.exp (-b) - Real.exp (-b - c)))) := by sorry

end SamuelCahnProphet.IID
