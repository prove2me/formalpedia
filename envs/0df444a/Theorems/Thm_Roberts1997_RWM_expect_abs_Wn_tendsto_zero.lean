-- Prove2me | Theorems.Thm_Roberts1997_RWM_expect_abs_Wn_tendsto_zero
-- name    : Roberts1997.RWM.expect_abs_Wn_tendsto_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:47:28.781132+00:00
-- url     : https://prove2.me/theorems/a30386b7-52ff-4a10-887d-73b7067cdb79
-- title:
--   Lemma 2.3 — sup over F_n of 𝔼|W_n| tends to 0
-- statement:
--   Let $f$ satisfy the standing hypotheses and $l>0$. For $x\in\mathbb R^n$ let $Y\sim N(x,\frac{l^2}{n-1}I_n)$, so that $Y_i\sim N(x_i,l^2/(n-1))$ independently, and let
--
--   $$ W_n=\sum_{i=2}^n\Big[\frac{(\log f(x_i))''}{2}(Y_i-x_i)^2+\frac{l^2}{2(n-1)}\big((\log f(x_i))'\big)^2\Big]. $$
--
--   Then $\sup_{x\in F_n}\mathbb E[|W_n|]\to0$ as $n\to\infty$: for every $\varepsilon>0$, for all sufficiently large $n$ and all $x\in F_n$, $W_n$ is integrable and
--
--   $$ \mathbb E\big[|W_n|\big]\le\varepsilon . $$
--
--   $W_n$ is the second-order part of the log acceptance ratio in coordinates $2,\dots,n$; the lemma shows it is negligible uniformly on $F_n$.
--
--   **Formalization Note** "$\sup_{x\in F_n}\mathbb E|W_n|\to0$" is stated as eventual uniform smallness, which is equivalent and avoids a real supremum (whose value on an empty or unbounded set is a default). Integrability is stated so the bound is not satisfied by a default value of the integral. The expectation is over the full proposal $Y\in\mathbb R^n$; $W_n$ does not involve $Y_1$.
-- source:
--   Roberts, Gelman, Gilks, Weak convergence and optimal scaling of random walk Metropolis algorithms, Ann. Appl. Probab. 7(1), 1997, p. 115, Lemma 2.3

import Definitions.Def_Roberts1997_RWM_IsRegularTarget
import Definitions.Def_Roberts1997_RWM_ProofObjects

open MeasureTheory ProbabilityTheory Filter

namespace Roberts1997.RWM

/-- Lemma 2.3 (p. 115). With `Y ~ N(x, σ_n² I_n)` (so `Y_i ~ N(x_i, l²/(n-1))` independently),
`sup_{x ∈ F_n} 𝔼[|W_n|] → 0` as `n → ∞`; stated as eventual uniform smallness, with
integrability of `W_n`. -/
theorem expect_abs_Wn_tendsto_zero (f : ℝ → ℝ) (hf : IsRegularTarget f) (l : ℝ) (hl : 0 < l) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x ∈ Fn f n,
      Integrable (Wn f n l x) (proposal n l x) ∧
      ∫ y, |Wn f n l x y| ∂(proposal n l x) ≤ ε := by sorry

end Roberts1997.RWM
