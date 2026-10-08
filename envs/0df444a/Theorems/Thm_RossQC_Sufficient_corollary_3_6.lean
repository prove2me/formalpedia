-- Prove2me | Theorems.Thm_RossQC_Sufficient_corollary_3_6
-- name    : RossQC.Sufficient.corollary_3_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:03.556838+00:00
-- url     : https://prove2.me/theorems/2cc38430-0df4-42bb-8bf7-9a8faa0eed06
-- title:
--   Corollary 3.6 — Lipschitz bounds for discounted value
-- statement:
--   Let $0<\beta<1$, $0\le\pi\le1$, and $0<C<I<R$. For any beliefs $P_1,P_2\in[0,1]$,
--   $$
--   |V_\beta(P_1)-V_\beta(P_2)|\le\frac{C|P_1-P_2|}{1-\beta(1-\pi)},
--   $$
--   and, when $\pi>0$, moreover $\dfrac{C|P_1-P_2|}{1-\beta(1-\pi)}\le\dfrac{C|P_1-P_2|}{\pi}$.
--
--   The first inequality supplies the belief sensitivity estimate used in Theorem 3.7(b); the second gives a discount-independent upper bound when $\pi>0$.
--
--   **Formalization Note** At $\pi=0$ the printed right-hand side $C|P_1-P_2|/\pi$ is $+\infty$ and the second inequality is trivial; Lean's convention $x/0=0$ would make it false, so the second inequality is stated under $\pi>0$ while the first is stated for every $\pi\in[0,1]$.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 592, Corollary 3.6

import Definitions.Def_RossQC_Sufficient_Model

namespace RossQC.Sufficient

/-- Ross, Corollary 3.6, p. 592. The first bound is stated for every
`π ∈ [0,1]`. The second displayed bound divides by `π`; at `π = 0` the page's
right side is `+∞` and the inequality is trivial, while Lean's `x / 0 = 0`
would make it false, so the second bound is stated under `0 < π`. -/
theorem corollary_3_6 (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R)
    (P₁ P₂ : ℝ) (hP₁ : P₁ ∈ Set.Icc (0 : ℝ) 1)
    (hP₂ : P₂ ∈ Set.Icc (0 : ℝ) 1) :
    |M.value P₁ - M.value P₂| ≤
      M.C * |P₁ - P₂| / (1 - M.β * (1 - M.π)) ∧
    (0 < M.π → M.C * |P₁ - P₂| / (1 - M.β * (1 - M.π)) ≤
      M.C * |P₁ - P₂| / M.π) := by sorry

end RossQC.Sufficient
