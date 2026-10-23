-- Prove2me | Theorems.Thm_QuadMemory_ConvexOpt_proposition_10
-- name    : QuadMemory.ConvexOpt.proposition_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:17.40258+00:00
-- url     : https://prove2.me/theorems/b97f0431-42c9-4257-8db4-5f7880cefb7c
-- title:
--   Proposition 10, p. 17 — a successful algorithm for the procedure ends the period p_max with probability ≥ q − C√(log d)/d
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $1\le k\le d/3-1$ with $p_{max}\ge1$ and let the cells of $\mathcal D_\delta$ have diameter at most $1/d^3$. Let $alg$ be successful for the optimization procedure with probability $q\in[0,1]$ and precision $\eta/(2\sqrt d)$ (Definition 6), and suppose that $alg$ performs at most $d^2$ queries during the optimization procedure. Then, when running $alg$ with the responses of the optimization procedure, $alg$ succeeds and ends the period $p_{max}$ with probability at least
--   $$q-\frac{C\sqrt{\log d}}d .$$
--
--   To succeed, an algorithm has to complete the whole construction, that is, to find $k$ exploratory directions in each of the $p_{max}$ periods.
--
--   **Formalization Note.** "Performs at most $d^2$ queries" is read as: on every realization of the procedure the algorithm stops by iteration $d^2$. "Ends the period $p_{max}$" means the procedure reached line 22.
-- source:
--   Blanchard, Zhang & Jaillet, arXiv:2302.04963v2, p. 17, Proposition 10 (proof pp. 17–18)

import Mathlib
import Definitions.Def_QuadMemory_ConvexOpt_Model
import Definitions.Def_QuadMemory_ConvexOpt_Game
import Definitions.Def_QuadMemory_ConvexOpt_Procedure

namespace QuadMemory.ConvexOpt

/-- Proposition 10 (p. 17): there is a universal `C > 0` such that, if `alg` is successful for the
optimization procedure with probability `q ∈ [0, 1]` and precision `η/(2√d)` and always stops
within `d²` queries during the procedure, then with probability at least `q - C √(log d)/d`
it succeeds and the procedure ends the period `p_max`. -/
theorem proposition_10 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d k M : ℕ), 1 ≤ k → (k : ℝ) ≤ (d : ℝ) / 3 - 1 → 1 ≤ pmax d k →
      ∀ (D : SphereDisc d), D.DiamLe (1 / (d : ℝ) ^ 3) → ∀ (alg : MemAlg d M) (q : ℝ),
        0 ≤ q → q ≤ 1 → ProcSuccess alg k D q (eta d / (2 * Real.sqrt d)) →
        (∀ (A : SignMatrix d) (w : Fin d → D.ι), ∃ T : ℕ, 1 ≤ T ∧ T ≤ d ^ 2 ∧
          alg.halt (procRun alg k D A w T).mem = true) →
        ENNReal.ofReal (q - C * Real.sqrt (Real.log d) / d) ≤
          procProb alg k D (fun A w =>
            ProcSucceeds alg k D (eta d / (2 * Real.sqrt d)) A w ∧
              EndsLastPeriod alg k D A w) := by sorry

end QuadMemory.ConvexOpt
