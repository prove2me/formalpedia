-- Prove2me | Theorems.Thm_QuadMemory_ConvexOpt_proposition_11
-- name    : QuadMemory.ConvexOpt.proposition_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:43.741149+00:00
-- url     : https://prove2.me/theorems/ccca8427-cf7d-4d2c-8fb9-80ebdacccd30
-- title:
--   Proposition 11, p. 18 — an M-bit algorithm successful for the procedure within m p_max queries gives a Game 2 strategy winning with probability ≥ q − C√(log d)/d
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $1\le k\le d/3-1$ with $p_{max}\ge1$, let the cells of $\mathcal D_\delta$ have diameter at most $1/d^3$, and let $m\le d$. Suppose that there is an $M$-bit algorithm that is successful for the optimization procedure with probability $q$ for accuracy $\epsilon=\eta/(2\sqrt d)$ and uses at most $mp_{max}$ queries. Then there is an algorithm for Game 2 with parameters
--   $$\Big(d,k,m,M,\ \alpha=\frac{2\eta}{\gamma_1},\ \beta=\frac{\gamma_2}4\Big)$$
--   for which the Player wins with probability at least $q-C\sqrt{\log d}/d$.
--
--   Some period of the procedure uses at most $m$ queries; the Player stores the algorithm's memory at the start of that period as its message and replays the period in the second phase of the game.
--
--   **Formalization Note.** "Uses at most $mp_{max}$ queries" is read as: on every realization of the procedure the algorithm stops by iteration $mp_{max}$. The Game 2 strategy uses the same discretization as the procedure.
-- source:
--   Blanchard, Zhang & Jaillet, arXiv:2302.04963v2, p. 18, Proposition 11 (proof pp. 18–22, Algorithm 3)

import Mathlib
import Definitions.Def_QuadMemory_ConvexOpt_Model
import Definitions.Def_QuadMemory_ConvexOpt_Game
import Definitions.Def_QuadMemory_ConvexOpt_Procedure

namespace QuadMemory.ConvexOpt

/-- Proposition 11 (p. 18): there is a universal `C > 0` such that, for `m ≤ d`, if an `M`-bit
algorithm is successful for the optimization procedure with probability `q` and accuracy
`η/(2√d)` and always stops within `m p_max` queries, then some strategy for Game 2 with parameters
`(d, k, m, M, α = 2η/γ₁, β = γ₂/4)` wins with probability at least `q - C √(log d)/d`. -/
theorem proposition_11 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d k m M : ℕ), 1 ≤ k → (k : ℝ) ≤ (d : ℝ) / 3 - 1 → 1 ≤ pmax d k →
      m ≤ d → ∀ (D : SphereDisc d), D.DiamLe (1 / (d : ℝ) ^ 3) → ∀ (alg : MemAlg d M) (q : ℝ),
        0 ≤ q → q ≤ 1 → ProcSuccess alg k D q (eta d / (2 * Real.sqrt d)) →
        (∀ (A : SignMatrix d) (w : Fin d → D.ι), ∃ T : ℕ, 1 ≤ T ∧ T ≤ m * pmax d k ∧
          alg.halt (procRun alg k D A w T).mem = true) →
        ∃ P : Player d k m M D,
          ENNReal.ofReal (q - C * Real.sqrt (Real.log d) / d) ≤
            winProb P (2 * eta d / gamma1 d) (gamma2 d / 4) := by sorry

end QuadMemory.ConvexOpt
