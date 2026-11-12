-- Prove2me | Theorems.Thm_SepQPTardos_Main_lemma_4_1
-- name    : SepQPTardos.Main.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:13:40.018631+00:00
-- url     : https://prove2.me/theorems/02564d88-76d2-4931-83a1-4890a65280f4
-- title:
--   Lemma 4.1 — covering bound $\|z^0-t\|_\infty\le\kappa E_F$
-- statement:
--   In the context of §4, let $t$ be a trial point and $E_F=\max(\alpha_F,V_F)$, $\kappa=mG$. Then there is an optimum $z^0$ on $P_F(b)$ with
--
--   $$\|z^0-t\|_\infty\le\kappa E_F.\tag{21}$$
--
--   Hence the box of radius $\kappa E_F$ around $t$ contains a relaxed optimum, which is the promise of Proposition 3.1 in the revelation step.
--
--   Differences from the source:
--   - generalization: A ∈ ℤ^{r×m}, rational b, c, q → integer A, real b, c, q; reason: the argument uses no rationality of b, c, q; rational data are a special case
--   - generalization: §4 runs under (7): feasible and finite, 1 ≤ r < m, N ≠ ∅, and after deleting redundant rows of A → none of these assumed; only q ≥ 0, an optimal pair (x*, π*) satisfying (8), and F ⊆ T*; reason: the argument does not use them; an instance satisfying (7) is a special case
--   - generalization: a basic optimal solution of (15) and the solution of (17) returned by rational elimination → every optimal solution (u, α_F) of (15) and every solution t of (17) built from it; reason: the argument uses only optimality in (15) and the equations (17); the paper's choice is one instance
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §4.3, Lemma 4.1, eq. (21), p. 9

import Mathlib
import Definitions.Def_SepQPTardos_Main_Problem
import Definitions.Def_SepQPTardos_Main_Circuits
import Definitions.Def_SepQPTardos_Main_Analysis

open Matrix

namespace SepQPTardos.Main

/-- Lemma 4.1 (covering bound; Cui–Li–Miao, STOC 2027 #829, p. 9). In the context of §4, for a
trial point `t` there is an optimum `z⁰` on `P_F(b)` with `‖z⁰ − t‖∞ ≤ κE_F`, `κ = mG`
(eq. (21)). -/
theorem lemma_4_1 {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℝ)
    (q c : Fin m → ℝ) (xs : Fin m → ℝ) (πs : Fin r → ℝ) (F : Finset (Fin m))
    (hctx : Sec4Context A b q c xs πs F) (t : Fin m → ℝ) (ht : IsTrialPoint A b q c F t) :
    ∃ z₀, IsMinimizer (PF A b F) (Phi q c) z₀ ∧
      ∀ e, |z₀ e - t e| ≤ (kappa A : ℝ) * EF A b q c F t := by sorry

end SepQPTardos.Main
