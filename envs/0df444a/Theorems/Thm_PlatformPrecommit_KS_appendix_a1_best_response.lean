-- Prove2me | Theorems.Thm_PlatformPrecommit_KS_appendix_a1_best_response
-- name    : PlatformPrecommit.KS.appendix_a1_best_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:44.792128+00:00
-- url     : https://prove2.me/theorems/94c150de-3e75-4323-a807-1ead35131069
-- title:
--   Online Appendix §A.1, p. 1 — joint price-and-wage best response (A.1)–(A.3)
-- statement:
--   Fix a nonnegative capacity profile $q$, a platform $i$ with positive capacity $q_i$, and its rival's price $p_j$ and wage $w_j$. Suppose $\Omega+\gamma p_j-\beta w_j>0$. In the capacity subgame, the unique joint price-and-wage best response is obtained by setting
--
--   $$z_i^*=\min\left\{q_i,\frac{\Omega+\gamma p_j-\beta w_j}{4}\right\},\qquad p_i^*=\Omega+\gamma p_j-z_i^*,\qquad w_i^*=z_i^*+\beta w_j.$$
--
--   Every other price-and-wage pair gives no more profit, and equality of profit forces that pair to equal $(p_i^*,w_i^*)$. The maximal profit is $(\Omega+\gamma p_j-\beta w_j-2z_i^*)z_i^*$.
--
--   This is the subgame optimization underlying the capacity analysis in Online Appendix §A.
--
--   **Formalization Note** Positive capacity and positive residual market are necessary for uniqueness. With zero capacity, every price-and-wage pair yields zero matches; with nonpositive residual market, zero-profit maximizers need not be unique. The rival profile is held fixed while one platform changes price and wage jointly.
-- source:
--   Hu, Liu, Precommitments in Two-Sided Market Competition, submitted manuscript (SSRN 3734828; TSpace), Online Appendix p. 1, §A.1, (A.1)–(A.3)

import Mathlib
import Definitions.Def_PlatformPrecommit_KS_Setting

namespace PlatformPrecommit.KS

/-- Online Appendix §A.1, (A.1)–(A.3): unique joint price-and-wage best response. -/
theorem appendix_a1_best_response (M : Model) (hM : M.Standing)
    (q : Fin 2 → ℝ) (pw : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (i : Fin 2)
    (hqAll : ∀ j, 0 ≤ q j) (hq : 0 < q i)
    (hmarket : 0 < M.Ω + M.γ * pw.1 (rival i) - M.β * pw.2 (rival i)) :
    let z : ℝ := min (q i)
      ((M.Ω + M.γ * pw.1 (rival i) - M.β * pw.2 (rival i)) / 4)
    let pStar : ℝ := M.Ω + M.γ * pw.1 (rival i) - z
    let wStar : ℝ := z + M.β * pw.2 (rival i)
    let best := (Function.update pw.1 i pStar, Function.update pw.2 i wStar)
    (∀ a b : ℝ,
      M.ksProfit q (Function.update pw.1 i a, Function.update pw.2 i b) i ≤
        M.ksProfit q best i ∧
      (M.ksProfit q (Function.update pw.1 i a, Function.update pw.2 i b) i =
        M.ksProfit q best i → a = pStar ∧ b = wStar)) ∧
    M.ksProfit q best i =
      (M.Ω + M.γ * pw.1 (rival i) - M.β * pw.2 (rival i) - 2 * z) * z := by sorry

end PlatformPrecommit.KS
