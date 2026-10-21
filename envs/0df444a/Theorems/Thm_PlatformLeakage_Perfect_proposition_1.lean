-- Prove2me | Theorems.Thm_PlatformLeakage_Perfect_proposition_1
-- name    : PlatformLeakage.Perfect.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:30.020184+00:00
-- url     : https://prove2.me/theorems/de42fc54-f91f-49c5-a2d1-15c76791df19
-- title:
--   Proposition 1, p. 16 — N^j_p(ω) ∈ {0, N^j}: none join iff ω < K̂^j/g2(1, v^j), all join iff ω ≥ K̂^j/g2(N^j, v^j)
-- statement:
--   Under the standing assumptions, fix a type $j$ and a payout ratio $\omega\in[0,1]$, and recall $\widehat K^j=\max\{K^j,g_2(1,(v^j-R_o)^+)\}$.
--
--   1. In every provider participation equilibrium $(N_p,N_o)$ at $\omega$, either $N_p=0$ or $N_p=N^j$.
--   2. A participation equilibrium with $N_p=0$ exists if and only if $\omega<\widehat K^j/g_2(1,v^j)$.
--   3. A participation equilibrium with $N_p=N^j$ exists if and only if $\omega\ge\widehat K^j/g_2(N^j,v^j)$.
--   4. A selected participation equilibrium exists, and the selected on-platform head count is
--   $$N^j_p(\omega)=\begin{cases}N^j,&\omega\ge\widehat K^j/g_2(N^j,v^j),\\0,&\text{otherwise.}\end{cases}$$
--
--   Providers either all join or all stay away: the off-platform option and the outside option merge into one non-platform option with cost $\widehat K^j$. Parts 1–3 are (22); part 4 adds the selection rule of p. 16.
--
--   **Formalization Note** Definition 1 is used without the printed clause $U^j_o<U^j_p(\omega,N^j_p-1)$ (see the model definition).
-- source:
--   He, Savin, Goh & Teo, Off-Platform Threats in On-Demand Services, SSRN working paper 3550646 (PDF of 2021-03-25), p. 16 (PDF 16), Proposition 1, (22), and the selection rule on p. 16; proof, Appendix p. 2 (PDF 37)

import Mathlib
import Definitions.Def_PlatformLeakage_Perfect_Model

namespace PlatformLeakage.Perfect

/-- Proposition 1 (p. 16): for a payout ratio `ω ∈ [0,1]`, every participation equilibrium has either
no or all `j`-type providers on the platform; an equilibrium with none exists iff `ω < K̂^j/g2(1, v^j)`,
one with all exists iff `ω ≥ K̂^j/g2(N^j, v^j)`; a selected equilibrium exists, and the selected
on-platform head count is `N^j` if `ω ≥ K̂^j/g2(N^j, v^j)` and `0` otherwise. -/
theorem proposition_1 (P : Params) (hP : P.Std) (j : PType) (ω : ℝ) (hω : ω ∈ Set.Icc (0 : ℝ) 1) :
    (∀ Np No : ℕ, IsPartEq P j ω Np No → Np = 0 ∨ Np = P.N j) ∧
    ((∃ No : ℕ, IsPartEq P j ω 0 No) ↔ ω < Khat P j / g2 P 1 (P.v j)) ∧
    ((∃ No : ℕ, IsPartEq P j ω (P.N j) No) ↔ Khat P j / g2 P (P.N j) (P.v j) ≤ ω) ∧
    (∃ Np No : ℕ, IsSelectedEq P j ω Np No) ∧
    selNp P j ω = (if Khat P j / g2 P (P.N j) (P.v j) ≤ ω then P.N j else 0) := by sorry

end PlatformLeakage.Perfect
