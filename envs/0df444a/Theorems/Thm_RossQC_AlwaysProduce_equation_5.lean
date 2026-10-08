-- Prove2me | Theorems.Thm_RossQC_AlwaysProduce_equation_5
-- name    : RossQC.AlwaysProduce.equation_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:25.019179+00:00
-- url     : https://prove2.me/theorems/4a1987dd-a19b-4410-94dc-b7789d69025b
-- title:
--   Equation (5) — discounted cost of always producing
-- statement:
--   For $0<\beta<1$, $0\le\pi\le1$, $0<C<I<R$, and an initial bad-state probability $P\in[0,1]$, let $R^0$ always produce without inspection. Its discounted expected cost is the series $\psi(P)=\sum_{n=0}^{\infty}\beta^n C T^nP$. Equation (5) evaluates it as
--
--   $$
--   \psi(P)=\frac{C}{1-\beta}-\frac{C(1-P)}{1-\beta(1-\pi)}.
--   $$
--
--   The identity permits a direct comparison between the cost of $R^0$ and the optimal value. The definition of $\psi$ remains the series; the closed form is the theorem's conclusion.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 591, §3 equation (5)

import Mathlib
import Definitions.Def_RossQC_AlwaysProduce_Model

namespace RossQC.AlwaysProduce

/-- Ross, *Quality Control under Markovian Deterioration*, §3, equation (5),
p. 591. Formalization Note: `psi` is the infinite series defining the cost
of the always-produce policy; its closed form is the conclusion here. -/
theorem equation_5 (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ∀ P ∈ Set.Icc (0 : ℝ) 1,
      M.psi P = M.C / (1 - M.β) -
        M.C * (1 - P) / (1 - M.β * (1 - M.π)) := by sorry

end RossQC.AlwaysProduce
