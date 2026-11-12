-- Prove2me | Theorems.Thm_SepQPTardos_Main_lemma_4_2
-- name    : SepQPTardos.Main.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:13:37.343537+00:00
-- url     : https://prove2.me/theorems/bdf2ecd7-f066-48cd-830a-cd63ba05b34b
-- title:
--   Lemma 4.2 — progress bound $E_F\le m\kappa\,\rho_F(z)$
-- statement:
--   In the context of §4, let $t$ be a trial point, $E_F=\max(\alpha_F,V_F)$ and $\kappa=mG$. Then every optimum $z$ on $P_F(b)$ satisfies
--
--   $$E_F\le m\kappa\,\rho_F(z),\qquad \rho_F(z)=\max_{e\notin F}z_e .\tag{23}$$
--
--   So when $E_F>0$ every relaxed optimum has an external coordinate of size at least $E_F/(m\kappa)$, which the local solver then detects.
--
--   Differences from the source:
--   - generalization: A ∈ ℤ^{r×m}, rational b, c, q → integer A, real b, c, q; reason: the argument uses no rationality of b, c, q; rational data are a special case
--   - generalization: §4 runs under (7): feasible and finite, 1 ≤ r < m, N ≠ ∅, and after deleting redundant rows of A → none of these assumed; only q ≥ 0, an optimal pair (x*, π*) satisfying (8), and F ⊆ T*; reason: the argument does not use them; an instance satisfying (7) is a special case
--   - generalization: a basic optimal solution of (15) and the solution of (17) returned by rational elimination → every optimal solution (u, α_F) of (15) and every solution t of (17) built from it; reason: the argument uses only optimality in (15) and the equations (17); the paper's choice is one instance
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §4.3, Lemma 4.2, eq. (23), p. 9 (proof pp. 9–10)

import Mathlib
import Definitions.Def_SepQPTardos_Main_Problem
import Definitions.Def_SepQPTardos_Main_Circuits
import Definitions.Def_SepQPTardos_Main_Analysis

open Matrix

namespace SepQPTardos.Main

/-- Lemma 4.2 (progress bound; Cui–Li–Miao, STOC 2027 #829, p. 9). In the context of §4, for a
trial point `t`, every optimum `z` on `P_F(b)` satisfies `E_F ≤ mκ ρ_F(z)` (eq. (23)). -/
theorem lemma_4_2 {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℝ)
    (q c : Fin m → ℝ) (xs : Fin m → ℝ) (πs : Fin r → ℝ) (F : Finset (Fin m))
    (hctx : Sec4Context A b q c xs πs F) (t : Fin m → ℝ) (ht : IsTrialPoint A b q c F t) :
    ∀ z, IsMinimizer (PF A b F) (Phi q c) z →
      EF A b q c F t ≤ (m : ℝ) * (kappa A : ℝ) * rhoF F z := by sorry

end SepQPTardos.Main
