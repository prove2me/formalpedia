-- Prove2me | Theorems.Thm_SamuelCahnProphet_IID_tendsto_W_one
-- name    : SamuelCahnProphet.IID.tendsto_W_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:21:52.863844+00:00
-- url     : https://prove2.me/theorems/e397ef24-2372-49a0-8707-385aec2ad53e
-- title:
--   Proof of Theorem 2, p. 1215 — W(1) = lim EX⁽ⁿ⁾_{t(1)} = 1 − e^{−b}
-- statement:
--   Fix reals $0 < a < 1$, $b > 0$, $c > 0$, and let $X_1^{(n)}, \dots, X_n^{(n)}$ be i.i.d., taking the values $0$, $a$ and $1$ with probabilities $1 - (b+c)/n$, $c/n$ and $b/n$. For the threshold rule $t(1)$ (stop at the first $i < n$ with $X_i^{(n)} \ge 1$, otherwise at $n$),
--   $$
--   W(1) = \lim_{n \to \infty} E X^{(n)}_{t(1)} = 1 - e^{-b}.
--   $$
--
--   This is the asymptotic value of the second of the two competing threshold rules of the extremal example.
--
--   **Formalization Note.** The sequence is indexed by $n = k + 1$; the terms with $n < b + c$ do not affect the limit. The expectation is in $[0, \infty]$, converted with `toReal`.
-- source:
--   Samuel-Cahn, Comparison of threshold stop rules and maximum for independent nonnegative random variables, Ann. Probab. 12 (1984), p. 1215, proof of Theorem 2, display W(1)

import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting

open MeasureTheory Filter Topology

namespace SamuelCahnProphet.IID

theorem tendsto_W_one (a b c : ℝ) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun k : ℕ => (EstopT (threePoint ((k + 1 : ℕ) : ℝ) a b c) (k + 1) 1).toReal) atTop
      (𝓝 (1 - Real.exp (-b))) := by sorry

end SamuelCahnProphet.IID
