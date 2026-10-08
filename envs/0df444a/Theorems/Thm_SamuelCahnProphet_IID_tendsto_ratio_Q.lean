-- Prove2me | Theorems.Thm_SamuelCahnProphet_IID_tendsto_ratio_Q
-- name    : SamuelCahnProphet.IID.tendsto_ratio_Q
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:21:54.344984+00:00
-- url     : https://prove2.me/theorems/c4a91ea3-e688-470b-a716-a81e71a04993
-- title:
--   Proof of Theorem 2, p. 1215 — Q(b, c) = lim E(Xₙ⁽ⁿ⁾*)/sup_{t∈T*ₙ} EX_t⁽ⁿ⁾
-- statement:
--   Fix reals $b > 0$, $c > 0$, put $a = a^*(b, c)$ (the value of the preceding milestone), and let $X_1^{(n)}, \dots, X_n^{(n)}$ be i.i.d., taking the values $0$, $a$ and $1$ with probabilities $1 - (b+c)/n$, $c/n$ and $b/n$. Then
--   $$
--   Q(b, c) = \lim_{n \to \infty} \frac{E(X_n^{(n)*})}{\sup_{t \in T_n^*} EX_t^{(n)}} = 1 + \frac{e^{-b} - e^{-b-c}}{1 - e^{-b-c}} - \frac{b(e^{-b} - e^{-b-c})^2}{c(1 - e^{-b-c})(1 - e^{-b})}.
--   $$
--
--   This is the asymptotic ratio of the prophet's value to the best threshold value in the extremal example.
--
--   **Formalization Note.** The sequence is indexed by $n = k + 1$, and both expectations are converted to reals with `toReal` before dividing. For $n > b + c$ both are finite (at most $1$) and the supremum is positive, so the ratio is the page's; the finitely many earlier terms do not affect the limit.
-- source:
--   Samuel-Cahn, Comparison of threshold stop rules and maximum for independent nonnegative random variables, Ann. Probab. 12 (1984), p. 1215, proof of Theorem 2, display Q(b, c)

import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting

open MeasureTheory Filter Topology

namespace SamuelCahnProphet.IID

theorem tendsto_ratio_Q (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun k : ℕ =>
        (Emax (threePoint ((k + 1 : ℕ) : ℝ) (aStarIID b c) b c) (k + 1)).toReal /
          (supE (threePoint ((k + 1 : ℕ) : ℝ) (aStarIID b c) b c) (k + 1)).toReal) atTop
      (𝓝 (Q b c)) := by sorry

end SamuelCahnProphet.IID
