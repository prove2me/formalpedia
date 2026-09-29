-- Prove2me | Theorems.Thm_TamingMonster_CoordDescent_coordinateDescent_halts_solves_OP
-- name    : TamingMonster.CoordDescent.coordinateDescent_halts_solves_OP
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T09:31:56.357583+00:00
-- url     : https://prove2.me/theorems/b6e2c519-17ba-45ea-bdd5-af075247ba06
-- title:
--   Theorem 3 — coordinate descent (Algorithm 2) from $Q_{\mathrm{init}}=\mathbf 0$ halts within $4\ln(1/(K\mu))/\mu$ iterations and solves (OP)
-- statement:
--   Let $K\ge1$ actions, a finite nonempty policy class $\Pi$, a history $H_t$ with $t\ge1$ records, and a minimum probability $\mu$ with $0<\mu\le1/(2K)$ be given. Run Algorithm 2 on $(H_t,\mu)$ with $Q_{\mathrm{init}}=\mathbf 0$, choosing in each Step 8 any policy $\pi$ with $D_\pi(Q)>0$.
--
--   1. **Iteration bound.** Every run executes Step 8 at most
--   $$\frac{4\ln\bigl(1/(K\mu)\bigr)}{\mu}$$
--   times. Since a state that does not halt always admits a further Step 8, every run halts after at most this many updates.
--   2. **Correctness.** When a run halts at Step 10, the weight vector it outputs is a solution of (OP): it lies in $\Delta^\Pi$ and satisfies Eqs. (2) and (3).
--
--   This is the paper's computational guarantee: (OP) is feasible, and a solution is found with a number of oracle calls that depends only on $K\mu$, not on $|\Pi|$ or $t$.
--
--   **Formalization Note** (i) "Iterations" counts executions of Step 8 (the paper's proof on p. 10 bounds "the number of times Step 8 is executed"); the final pass that halts at Step 10 is not counted. (ii) The bound is compared in $\mathbb R$ and not rounded. (iii) The printed statement uses $\mu_m$ of Algorithm 1; here $\mu$ is any value in $(0,1/(2K)]$, the range of $\mu_m$. (iv) The paper's history allows $p_i(a_i)\in[0,1]$; here $p_i(a_i)\in(0,1]$. (v) Algorithm 2 is encoded relationally: the bound holds for every run, whatever policy each Step 8 chooses.
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 6, Theorem 3 (proof p. 10, §5)

import Mathlib
import Definitions.Def_TamingMonster_CoordDescent_Setting
import Definitions.Def_TamingMonster_CoordDescent_Algorithm

namespace TamingMonster.CoordDescent

/-- Theorem 3 (p. 6): Algorithm 2 with `Q_init := 0` halts in at most `4 ln(1/(Kμ))/μ`
iterations and outputs a solution `Q` to (OP).
(i) Every run from `Q_init = 0`, whatever policy each Step 8 picks among those with
`D_π > 0`, executes Step 8 at most `4 ln(1/(Kμ))/μ` times; since a state that does not halt
always admits a further Step 8, every run halts within that many updates.
(ii) When a run halts, its output `rescale Q⁽ⁿ⁾` solves (OP). -/
theorem coordinateDescent_halts_solves_OP {X : Type*} {K t : ℕ} (hK : 0 < K) (ht : 0 < t)
    (Pi : Finset (X → Fin K)) (hPi : Pi.Nonempty) (H : History X K t)
    (μ : ℝ) (hμ : 0 < μ) (hμK : μ ≤ 1 / (2 * (K : ℝ))) :
    (∀ (n : ℕ) (Qs : ℕ → Pi → ℝ), IsRun Pi H μ (fun _ => 0) n Qs →
        (n : ℝ) ≤ 4 * Real.log (1 / ((K : ℝ) * μ)) / μ) ∧
    (∀ (n : ℕ) (Qs : ℕ → Pi → ℝ), IsRun Pi H μ (fun _ => 0) n Qs →
        HaltsAt Pi H μ (Qs n) → SolvesOP Pi H μ (rescale Pi H μ (Qs n))) := by sorry

end TamingMonster.CoordDescent
