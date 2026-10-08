-- Prove2me | Theorems.Thm_ProbMFG_Existence_proposition_2_5
-- name    : ProbMFG.Existence.proposition_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:51.852337+00:00
-- url     : https://prove2.me/theorems/aadbdd03-9c23-462c-a492-fda4bfc75bb7
-- title:
--   Proposition 2.5 — comparison across initial states and flows
-- statement:
--   Keep the assumptions of Theorem 2.2. Let a second admissible controlled diffusion $U'$ start at $x'_0$ and use another bounded flow $\mu'$ in its drift, while its cost still uses $\mu$. With $\hat a_t=\hat a(t,X_t,\mu_t,Y_t)$,
--   $$J(\hat a;\mu)+\langle x'_0-x_0,Y_0\rangle+\lambda\mathbb E\int_0^T\|\beta_t-\hat a_t\|^2dt\le J([\beta,\mu'];\mu)+\mathbb E\int_0^T\langle b_0(t,\mu'_t)-b_0(t,\mu_t),Y_t\rangle dt.$$
--   This is the comparison estimate used for stability under a changing measure flow.
--
--   **Formalization Note** The initial pairing is written inside an expectation; on the augmented Brownian filtration $Y_0$ is almost surely deterministic. The cost of $U'$ uses $\mu$ while its SDE uses $\mu'$.
-- source:
--   Carmona and Delarue, Probabilistic analysis of mean-field games, SIAM J. Control Optim. 51 (2013), p. 2712, Proposition 2.5, (2.15)–(2.16); https://doi.org/10.1137/120883499

import Mathlib
import Definitions.Def_ProbMFG_Existence_Model
import Definitions.Def_ProbMFG_Existence_Solution

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbMFG.Existence

/-- Proposition 2.5: the sufficient maximum principle comparing different
initial states and different measure flows in the controlled drift. -/
theorem proposition_2_5 {d m k : ℕ} (M : Model d m k) (lam cL : ℝ)
    (hlam : 0 < lam) (hcL : 0 < cL)
    (hA1 : M.A1) (hA2 : M.A2 lam cL) (hA3 : M.A3) (hA4 : M.A4 cL)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → Fin m → ℝ) (hW : Peng1990.SMP.IsStdBrownian P W)
    (μ μ' : ℝ≥0 → Measure (State d)) (X Y : StateProcess Ω d)
    (Z : NoiseProcess Ω d m) (hXYZ : M.SolvesFrozen P hW μ X Y Z)
    (hμ' : M.IsFlow μ') (x₀' : State d)
    (β : ℝ≥0 → Ω → Action k)
    (hβ : Peng1990.SMP.L2F (ReflectedBSDE.Existence.augmentedFiltration P hW) P M.T β)
    (U' : StateProcess Ω d) (hU' : M.IsControlled P hW μ' x₀' U' β) :
    M.cost P μ X (fun t ω => M.alphaHat t (X t ω) (μ t) (Y t ω)) +
      (∫ ω, inner ℝ (x₀' - M.x₀) (Y 0 ω) ∂P) +
      lam * (∫⁻ ω, ∫⁻ t in Set.Icc (0 : ℝ) M.T,
        ‖β t.toNNReal ω - M.alphaHat t.toNNReal (X t.toNNReal ω)
          (μ t.toNNReal) (Y t.toNNReal ω)‖ₑ ^ 2 ∂volume ∂P).toReal ≤
      M.cost P μ U' β +
        (∫ ω, ∫ t in Set.Icc (0 : ℝ) M.T,
          inner ℝ (M.b₀ t.toNNReal (μ' t.toNNReal) - M.b₀ t.toNNReal (μ t.toNNReal))
            (Y t.toNNReal ω) ∂volume ∂P) := by sorry

end ProbMFG.Existence
