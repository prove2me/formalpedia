-- Prove2me | Theorems.Thm_QuadMemory_ConvexOpt_proposition_9
-- name    : QuadMemory.ConvexOpt.proposition_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:33.392828+00:00
-- url     : https://prove2.me/theorems/e728d63a-add2-49a9-96a7-a8c06b7dbfe4
-- title:
--   Proposition 9, p. 14 — with probability ≥ 1 − C√(log d)/d, min over the ball of F_{A,v} is at most −η/(40√((k p_max + 1) log d))
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $1\le k\le d/3-1$ with $p_{max}\ge1$ and let the cells of $\mathcal D_\delta$ have diameter at most $1/d^3$. Let $A\sim\mathcal U(\{\pm1\}^{n\times d})$ and $v_0\sim\mathcal U(\mathcal D_\delta)$. For any algorithm $alg$ for convex optimization, let $v$ be the vectors constructed by the randomized procedure. With probability at least $1-C\sqrt{\log d}/d$ over $A$, $v_0$ and $v$,
--   $$\min_{x\in B_d(0,1)}F_{A,v}(x)\le-\frac{\eta}{40\sqrt{(kp_{max}+1)\log d}} .$$
--
--   The constructed function has a deep minimum, so an accurate output must lie well below the values that informative queries see before the last period ends.
--
--   **Formalization Note.** "$\min\le c$" is stated as the existence of a point of the ball with value at most $c$. $F_{A,v}$ is the function of all vectors constructed by the procedure.
-- source:
--   Blanchard, Zhang & Jaillet, arXiv:2302.04963v2, p. 14, Proposition 9 (proof pp. 14–17)

import Mathlib
import Definitions.Def_QuadMemory_ConvexOpt_Model
import Definitions.Def_QuadMemory_ConvexOpt_Game
import Definitions.Def_QuadMemory_ConvexOpt_Procedure

namespace QuadMemory.ConvexOpt

/-- Proposition 9 (p. 14): there is a universal `C > 0` such that, for `A ∼ U({±1}^{n×d})`,
`v_0 ∼ U(D_δ)` and any algorithm, with probability at least `1 - C √(log d)/d` the vectors `v`
constructed by Procedure 1 satisfy
`min_{x ∈ B_d(0,1)} F_{A,v}(x) ≤ -η / (40 √((k p_max + 1) log d))`. -/
theorem proposition_9 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d k M : ℕ), 1 ≤ k → (k : ℝ) ≤ (d : ℝ) / 3 - 1 → 1 ≤ pmax d k →
      ∀ (D : SphereDisc d), D.DiamLe (1 / (d : ℝ) ^ 3) → ∀ (alg : MemAlg d M),
        ENNReal.ofReal (1 - C * Real.sqrt (Real.log d) / d) ≤
          procProb alg k D (fun A w => ∃ x ∈ Metric.closedBall (0 : E d) 1,
            Ffinal alg k D A w x ≤
              -(eta d / (40 * Real.sqrt (((k : ℝ) * pmax d k + 1) * Real.log d)))) := by sorry

end QuadMemory.ConvexOpt
