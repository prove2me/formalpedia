-- Prove2me | Theorems.Thm_RossQC_AlwaysProduce_corollary_3_6
-- name    : RossQC.AlwaysProduce.corollary_3_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:51.633983+00:00
-- url     : https://prove2.me/theorems/bdfd7f0c-d20d-4a40-96fb-5342bd078774
-- title:
--   Corollary 3.6 — Lipschitz bound for the discounted value
-- statement:
--   Under $0<\beta<1$, $0\le\pi\le1$, and $0<C<I<R$, for any beliefs $P_1,P_2\in[0,1]$ the infinite-horizon value satisfies
--
--   $$
--   |V_\beta(P_1)-V_\beta(P_2)|\le\frac{C|P_1-P_2|}{1-\beta(1-\pi)}.
--   $$
--
--   When $\pi>0$, the right-hand side is at most $C|P_1-P_2|/\pi$. This gives continuity of $V_\beta$ on the belief interval, needed to interpret the strict conclusion near $P=1$ in Theorem 3.4(b).
--
--   **Formalization Note** The extra condition $\pi>0$ applies only to the second inequality; division by zero in Lean otherwise produces a total value that is not the paper's bound.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 592, Corollary 3.6

import Mathlib
import Definitions.Def_RossQC_AlwaysProduce_Model

namespace RossQC.AlwaysProduce

/-- Ross, *Quality Control under Markovian Deterioration*, Corollary 3.6,
p. 592. Formalization Note: the second bound requires `π > 0` because
division by zero in Lean is total; the first bound also covers `π = 0`. -/
theorem corollary_3_6 (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ∀ (P₁ P₂ : ℝ), P₁ ∈ Set.Icc (0 : ℝ) 1 → P₂ ∈ Set.Icc (0 : ℝ) 1 →
      |M.value P₁ - M.value P₂| ≤
        M.C * |P₁ - P₂| / (1 - M.β * (1 - M.π)) ∧
      (0 < M.π →
        M.C * |P₁ - P₂| / (1 - M.β * (1 - M.π)) ≤
          M.C * |P₁ - P₂| / M.π) := by sorry

end RossQC.AlwaysProduce
