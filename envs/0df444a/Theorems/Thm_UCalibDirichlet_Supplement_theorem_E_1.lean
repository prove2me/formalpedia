-- Prove2me | Theorems.Thm_UCalibDirichlet_Supplement_theorem_E_1
-- name    : UCalibDirichlet.Supplement.theorem_E_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:14:46.502341+00:00
-- url     : https://prove2.me/theorems/3a309f95-fb2f-4723-8eaa-2f8cfaef2287
-- title:
--   Theorem E.1 — accumulation bound $R^{\mathrm{LP}}_F(T)\lesssim\log(eT)+\sum_{t\le T}L_F(t)/t$
-- statement:
--   Let $K=2$ and let $F:[0,1]\to\mathbb R$ be convex, with $F'$ absolutely continuous on $[0,1]$ and $F''$ bounded on neighbourhoods of $0$ and $1$. Then there is a constant $C$, depending only on $F$, such that for every integer $T\ge 2$ the worst-case expected regret of Algorithm 1 (the Laplace forecaster) under the canonical loss $\ell_F(p,y)=-F(p)-F'(p)(y-p)$ satisfies
--   $$R^{\mathrm{LP}}_F(T)\ \le\ C\Big(\log(eT)+\sum_{t=1}^{T}\frac{L_F(t)}{t}\Big),$$
--   where $L_F(t)=t\sup_{p\in[0,1]}\{\mathbb E_{S\sim\mathrm{Bin}(t,p)}F(S/t)-F(p)\}$.
--
--   This refines the general bound of Theorem 1.8 in the binary case: the logarithmic loss of the general bound comes from accumulating stability terms, and the sum $\sum_t L_F(t)/t$ is what that accumulation costs.
--
--   **Formalization Note** $\lesssim$ hides a constant depending on $F$ but not on $T$ (Appendix E.1.1), so the constant is chosen after $F$ and before $T$.
--
--   Differences from the source:
--   - reading: R^LP_F(T) ≲ log(eT) + Σ L_F(t)/t for every integer T ≥ 2 → ∃ C (after F), ∀ T ≥ 2, R^LP ≤ C (log(eT) + Σ_{t=1}^T L_F(t)/t); reason: ≲ hides a constant depending on F but not on T (App. E.1.1)
--   - encoding: F′ absolutely continuous on [0,1], F″ bounded on neighborhoods of 0 and 1 → ACDerivBddEnds F; reason: the hypothesis presupposes F′ on [0,1]; curvature bounds are a.e. (App. E.1.1)
--   - encoding: R^LP_F(T), canonical loss, binary forecasts, L_F of (60) → lapRegret (canonLoss F) T with q ∈ Δ₂, p = q 1, and LF (pot2 F); reason: the canonical loss of App. E.1.1 and the base model at K = 2
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Theorem E.1, display (64), p.41

import Mathlib
import Definitions.Def_UCalibDirichlet_LF
import Definitions.Def_UCalibDirichlet_Supplement_pot2
import Definitions.Def_UCalibDirichlet_Supplement_canonLoss
import Definitions.Def_UCalibDirichlet_Supplement_lapRegret
import Definitions.Def_UCalibDirichlet_Supplement_ACDerivBddEnds

namespace UCalibDirichlet.Supplement

/-- **Theorem E.1 (Accumulation bound).** Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027
submission), Theorem E.1, display (64), p.41: "Let `F′` be absolutely continuous on `[0, 1]`, with
`F` convex, and suppose `F″` is bounded on neighborhoods of 0 and 1. Then, for every integer
`T ≥ 2`, `R^LP_F(T) ≲ log(eT) + ∑_{t=1}^T L_F(t)/t`. (64)"

For a binary convex potential `F` with `ACDerivBddEnds F` there is a constant `C` (depending on
`F`) such that for every integer `T ≥ 2`, the worst-case expected regret of Algorithm 1 under the
canonical loss satisfies
`R^LP_F(T) ≤ C (log(eT) + ∑_{t=1}^T L_F(t)/t)`.

**Formalization Note.** `≲` hides a constant that may depend on the fixed potential but not on `T`
(App. E.1.1, p.40), so `∃ C` comes after `F` and before `T`. `L_F` is the binary (60), the base
`LF (pot2 F)`; `R^LP_F` is `lapRegret (canonLoss F)`. -/
theorem theorem_E_1 (F : ℝ → ℝ) (hconv : ConvexOn ℝ (Set.Icc 0 1) F) (hF : ACDerivBddEnds F) :
    ∃ C : ℝ, ∀ T : ℕ, 2 ≤ T →
      lapRegret (canonLoss F) T ≤
        ((C * (Real.log (Real.exp 1 * T) + ∑ t ∈ Finset.Icc 1 T, LF (pot2 F) t / t) : ℝ) :
          EReal) := by sorry

end UCalibDirichlet.Supplement
