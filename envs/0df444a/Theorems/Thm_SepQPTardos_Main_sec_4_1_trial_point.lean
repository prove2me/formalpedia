-- Prove2me | Theorems.Thm_SepQPTardos_Main_sec_4_1_trial_point
-- name    : SepQPTardos.Main.sec_4_1_trial_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:13:25.086623+00:00
-- url     : https://prove2.me/theorems/a5b813cc-3e60-46bc-b0ca-4a337c41d15d
-- title:
--   §4.1, LP (15), (16) and system (17) — the trial point exists, lies in $P_F(b)$ and has small external coordinates
-- statement:
--   In the context of §4 ($q\ge0$, an optimal primal–dual pair $(x^*,\pi^*)$ of (1), $F\subseteq T^*$):
--
--   1. LP (15) — minimise $\alpha$ subject to $Au=b$, $0\le u_{\bar F}\le\alpha\mathbf 1$, $\alpha\ge0$, $u_F$ free — is feasible and attains its finite minimum $\alpha_F\ge0$;
--   2. $\alpha_F\le\rho_F(z)$ for every $z\in P_F(b)$, and $\alpha_F=0$ if $\bar F$ is empty (16);
--   3. for every optimal solution $(u,\alpha_F)$ of (15) the system (17), $t_{\bar F}=u_{\bar F}$, $A_Ft_F=b-A_{\bar F}u_{\bar F}$, $Q_Ft_F+c_F=A_F^\top\lambda$ for some $\lambda$, is consistent;
--   4. every such solution $t$ lies in $P_F(b)$ and satisfies $0\le t_{\bar F}\le\alpha_F\mathbf 1$.
--
--   The trial point $t$ is the centre of the local box in §4.4; stationarity on $F$ is the property Lemma 4.2 needs.
--
--   Differences from the source:
--   - generalization: A ∈ ℤ^{r×m}, rational b, c, q → integer A, real b, c, q; reason: the argument uses no rationality of b, c, q; rational data are a special case
--   - generalization: §4 runs under (7): feasible and finite, 1 ≤ r < m, N ≠ ∅, and after deleting redundant rows of A → none of these assumed; only q ≥ 0, an optimal pair (x*, π*) satisfying (8), and F ⊆ T*; reason: the argument does not use them; an instance satisfying (7) is a special case
--   - generalization: a basic optimal solution of (15) and the solution of (17) returned by rational elimination → every optimal solution (u, α_F) of (15) and every solution t of (17) built from it; reason: the argument uses only optimality in (15) and the equations (17); the paper's choice is one instance
--   - encoding: α_F, the optimal value of (15) → the infimum of the feasible values of α, with attainment asserted; reason: the infimum is the LP optimum once it is attained, which the statement asserts
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §4.1, LP (15), (16), system (17), p. 8

import Mathlib
import Definitions.Def_SepQPTardos_Main_Problem
import Definitions.Def_SepQPTardos_Main_Circuits
import Definitions.Def_SepQPTardos_Main_Analysis

open Matrix

namespace SepQPTardos.Main

/-- §4.1, LP (15), (16) and system (17) (Cui–Li–Miao, STOC 2027 #829, p. 8). In the context of
§4: LP (15) is feasible and attains its finite minimum `α_F ≥ 0`; `α_F ≤ ρ_F(z)` for every
`z ∈ P_F(b)`; `α_F = 0` if `F̄` is empty; for every optimal solution `(u, α_F)` of (15) the
system (17) with `v = u_{F̄}` is consistent; and every such solution `t` lies in `P_F(b)` with
`0 ≤ t_{F̄} ≤ α_F𝟙`. -/
theorem sec_4_1_trial_point {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℝ)
    (q c : Fin m → ℝ) (xs : Fin m → ℝ) (πs : Fin r → ℝ) (F : Finset (Fin m))
    (hctx : Sec4Context A b q c xs πs F) :
    (∃ u, IsLP15Opt A b F u) ∧ 0 ≤ alphaF A b F ∧
    (∀ z ∈ PF A b F, alphaF A b F ≤ rhoF F z) ∧
    (F = Finset.univ → alphaF A b F = 0) ∧
    (∀ u, IsLP15Opt A b F u → ∃ t, Sys17 A b q c F u t) ∧
    ∀ t, IsTrialPoint A b q c F t →
      t ∈ PF A b F ∧ ∀ e, e ∉ F → t e ≤ alphaF A b F := by sorry

end SepQPTardos.Main
