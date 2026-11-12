-- Prove2me | Theorems.Thm_SepQPTardos_Main_sec_4_4_revelation
-- name    : SepQPTardos.Main.sec_4_4_revelation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:13:24.237204+00:00
-- url     : https://prove2.me/theorems/729d7c59-64e7-40c6-a030-e3d4cc7b4781
-- title:
--   §4.4, steps 3–4 and (24) — each local call reveals a new tight coordinate
-- statement:
--   In the context of §4, let $t$ be a trial point and $E_F=\max(\alpha_F,V_F)$, $\kappa=mG$.
--
--   1. If $F$ contains every coordinate, then $E_F=0$.
--   2. Suppose $E_F>0$, and put $\varepsilon=E_F/(4m\kappa)$ and $B=4m\kappa^2$ (step 3). Then $B\varepsilon=\kappa E_F$, and the box $|x-t|\le B\varepsilon\mathbf 1$ contains an optimum on $P_F(b)$. Moreover, for every $x\in P_F(b)$ within $\ell_\infty$ distance $\varepsilon$ of some optimum on $P_F(b)$, the update (24)
--   $$F'=F\cup\{e\notin F: x_e>\varepsilon\}$$
--   satisfies $F\subsetneq F'$ and $F'\subseteq T^*$.
--
--   Thus the invariant $F\subseteq T^*$ is preserved and $F$ strictly grows on each call, so there are at most $m$ local calls.
--
--   Differences from the source:
--   - generalization: A ∈ ℤ^{r×m}, rational b, c, q → integer A, real b, c, q; reason: the argument uses no rationality of b, c, q; rational data are a special case
--   - generalization: §4 runs under (7): feasible and finite, 1 ≤ r < m, N ≠ ∅, and after deleting redundant rows of A → none of these assumed; only q ≥ 0, an optimal pair (x*, π*) satisfying (8), and F ⊆ T*; reason: the argument does not use them; an instance satisfying (7) is a special case
--   - generalization: a basic optimal solution of (15) and the solution of (17) returned by rational elimination → every optimal solution (u, α_F) of (15) and every solution t of (17) built from it; reason: the argument uses only optimality in (15) and the equations (17); the paper's choice is one instance
--   - reading: Thus some external coordinate has x_e ≥ 3ε > ε and is added ... F strictly grows. There are at most m local calls. → F ⊊ F' and F' ⊆ T*; reason: the count of at most m calls is the immediate consequence that a strictly growing subset of [m] grows at most m times
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §4.4, steps 3–4, update (24) and the paragraph following it, p. 10

import Mathlib
import Definitions.Def_SepQPTardos_Main_Problem
import Definitions.Def_SepQPTardos_Main_Circuits
import Definitions.Def_SepQPTardos_Main_Analysis

open Matrix

namespace SepQPTardos.Main

/-- §4.4, steps 3–4 and update (24) (Cui–Li–Miao, STOC 2027 #829, p. 10). In the context of §4,
for a trial point `t`: if `F` contains every coordinate then `E_F = 0`. If `E_F > 0`, put
`ε = E_F/(4mκ)` and `B = 4mκ²`; then `Bε = κE_F`, the box `|x − t| ≤ Bε𝟙` contains an optimum
on `P_F(b)`, and for every `x ∈ P_F(b)` within `ℓ∞` distance `ε` of some optimum on `P_F(b)`
the updated set `F' = F ∪ {e ∉ F : xₑ > ε}` satisfies `F ⊊ F'` and `F' ⊆ T*`. -/
theorem sec_4_4_revelation {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℝ)
    (q c : Fin m → ℝ) (xs : Fin m → ℝ) (πs : Fin r → ℝ) (F : Finset (Fin m))
    (hctx : Sec4Context A b q c xs πs F) (t : Fin m → ℝ) (ht : IsTrialPoint A b q c F t) :
    (F = Finset.univ → EF A b q c F t = 0) ∧
    (0 < EF A b q c F t →
      ((4 * m * kappa A ^ 2 : ℕ) : ℝ) * (EF A b q c F t / (4 * m * kappa A)) =
          (kappa A : ℝ) * EF A b q c F t ∧
      (∃ z₀, IsMinimizer (PF A b F) (Phi q c) z₀ ∧
        ∀ e, |z₀ e - t e| ≤
          ((4 * m * kappa A ^ 2 : ℕ) : ℝ) * (EF A b q c F t / (4 * m * kappa A))) ∧
      ∀ x ∈ PF A b F,
        (∃ z, IsMinimizer (PF A b F) (Phi q c) z ∧
          ∀ e, |x e - z e| ≤ EF A b q c F t / (4 * m * kappa A)) →
        F ⊂ F ∪ Finset.univ.filter (fun e => e ∉ F ∧ EF A b q c F t / (4 * m * kappa A) < x e) ∧
        ∀ e ∈ F ∪ Finset.univ.filter
            (fun e => e ∉ F ∧ EF A b q c F t / (4 * m * kappa A) < x e),
          slack (castMat A) q c xs πs e = 0) := by sorry

end SepQPTardos.Main
