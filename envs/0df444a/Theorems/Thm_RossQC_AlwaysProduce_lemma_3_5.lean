-- Prove2me | Theorems.Thm_RossQC_AlwaysProduce_lemma_3_5
-- name    : RossQC.AlwaysProduce.lemma_3_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:33.974288+00:00
-- url     : https://prove2.me/theorems/a8c31eb9-8b33-4400-a6f8-116762f239b8
-- title:
--   Lemma 3.5 — exact finite-horizon Lipschitz bound
-- statement:
--   Let $0<\beta<1$, $0\le\pi\le1$, and $0<C<I<R$. For any two beliefs $P_1,P_2\in[0,1]$ and any finite horizon $n\ge0$, the finite-horizon optimal costs obey
--
--   $$
--   |V^n(P_1)-V^n(P_2)|\le\frac{C|P_1-P_2|\bigl(1-[\beta(1-\pi)]^n\bigr)}{1-\beta(1-\pi)}.
--   $$
--
--   The factor retains the exact horizon dependence stated by Ross. It controls how changing the initial belief changes the finite-horizon value.
--
--   **Formalization Note** Ross begins with $n=1$ and $V^1=\min\{CP,I,R\}$. The defined iteration also has $V^0=0$, for which the inequality is equality.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 592, Lemma 3.5

import Mathlib
import Definitions.Def_RossQC_AlwaysProduce_Model

namespace RossQC.AlwaysProduce

/-- Ross, *Quality Control under Markovian Deterioration*, Lemma 3.5, p. 592.
Formalization Note: the paper's `V_β¹ = min {CP,I,R}` equals `valueIter 1`.
At `n = 0` both sides vanish, so including it does not alter the result. -/
theorem lemma_3_5 (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ∀ (n : ℕ) (P₁ P₂ : ℝ),
      P₁ ∈ Set.Icc (0 : ℝ) 1 → P₂ ∈ Set.Icc (0 : ℝ) 1 →
      |M.valueIter n P₁ - M.valueIter n P₂| ≤
        M.C * |P₁ - P₂| * (1 - (M.β * (1 - M.π)) ^ n) /
          (1 - M.β * (1 - M.π)) := by sorry

end RossQC.AlwaysProduce
