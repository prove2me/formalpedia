-- Prove2me | Theorems.Thm_RossQC_AlwaysProduce_theorem_3_4
-- name    : RossQC.AlwaysProduce.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:49.341448+00:00
-- url     : https://prove2.me/theorems/fc620142-b97e-45c2-a37d-0b89131207a5
-- title:
--   Theorem 3.4 — exactly when always producing is optimal
-- statement:
--   Consider the two-state deterioration model with $0<\beta<1$, $0\le\pi\le1$, and $0<C<I<R$. Write $R^0$ for the policy that always produces without inspection, $\psi(P)$ for its discounted cost, and $V_\beta(P)$ for the optimal discounted value. Then $R^0$ is optimal from every initial belief $P\in[0,1]$ exactly when
--
--   $$
--   R\ge\frac{C}{1-\beta(1-\pi)}.
--   $$
--
--   If $R<C/[1-\beta(1-\pi)]$, there is a one-sided neighborhood of $P=1$ within $[0,1]$ on which revision is strictly cheaper in the Bellman equation than either production or inspection. Thus every discounted-optimal policy revises there.
--
--   This gives an exact parameter boundary for when inspection and revision can both be omitted, and it identifies forced revision when the boundary fails.
--
--   **Formalization Note** “$R^0$ is optimal” means $\psi(P)=V_\beta(P)$ for every $P\in[0,1]$. “Every optimal policy revises” is stated as revision being the unique minimizing action. The positive bad-state cost $C>0$ is implicit in the model and explicit here.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 592, Theorem 3.4(a,b)

import Mathlib
import Definitions.Def_RossQC_AlwaysProduce_Model

namespace RossQC.AlwaysProduce

/-- Ross, *Quality Control under Markovian Deterioration*, Theorem 3.4(a,b),
p. 592. Formalization Note: `psi` is the discounted series cost of `R⁰`;
`R⁰` is β-optimal exactly when it equals `value` throughout `[0,1]`.
“Every β-optimal policy revises” is represented by revision being the unique
minimizer of equation (3). “Near 1” is a one-sided neighborhood in `[0,1]`.
`0 < C` makes explicit the positive bad-state cost implicit in the model. -/
theorem theorem_3_4 (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ((∀ P ∈ Set.Icc (0 : ℝ) 1, M.psi P = M.value P) ↔
      M.C / (1 - M.β * (1 - M.π)) ≤ M.R) ∧
    (M.R < M.C / (1 - M.β * (1 - M.π)) →
      ∃ ε : ℝ, 0 < ε ∧
        ∀ P ∈ Set.Icc (0 : ℝ) 1, 1 - ε < P →
          M.rhs3 M.value P .revise < M.rhs3 M.value P .produce ∧
          M.rhs3 M.value P .revise < M.rhs3 M.value P .inspect) := by sorry

end RossQC.AlwaysProduce
