-- Prove2me | Theorems.Thm_UCalibDirichlet_Supplement_theorem_E_8
-- name    : UCalibDirichlet.Supplement.theorem_E_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:16:36.815561+00:00
-- url     : https://prove2.me/theorems/1c3b594a-efbe-4e07-a8b2-601be100abe5
-- title:
--   Theorem E.8 (= Theorem 1.16) — logarithmic gap: $L_F(T)=\Theta(\log eT)$, $R^*_F(T)\asymp R^{\mathrm{LP}}_F(T)\asymp(\log eT)^2$
-- statement:
--   Let
--   $$F(p)=\Big(p-\tfrac12\Big)^2\log\frac{e}{|p-\tfrac12|},\qquad F(\tfrac12)=0,$$
--   and let $\ell_F(p,y)=-F(p)-F'(p)(y-p)$ be its canonical binary loss. Then:
--
--   1. $F$ induces a bounded continuous proper loss: $\ell_F$ is proper with finite Bayes risk $-F$, there is $B$ with $|\ell_F(p,y)|\le B$ for all $p\in[0,1]$, $y\in\{0,1\}$, and each $\ell_F(\cdot,y)$ is continuous on $[0,1]$;
--   2. there are constants $c,C>0$ such that for every $T\ge 1$
--   $$c\log(eT)\le L_F(T)\le C\log(eT),$$
--   $$c\,(\log eT)^2\le R^*_F(T)\le C\,(\log eT)^2,\qquad c\,(\log eT)^2\le R^{\mathrm{LP}}_F(T)\le C\,(\log eT)^2,$$
--   where $L_F$ is the Bernstein gap (60), $R^*_F$ the minimax regret and $R^{\mathrm{LP}}_F$ the worst-case expected regret of Algorithm 1 (the Laplace forecaster).
--
--   So the i.i.d. lower bound $L_F(T)$ of Theorem 1.8 is off by a logarithmic factor for this loss, while Algorithm 1 remains minimax optimal in $T$. Theorem 1.16 of the introduction is the same result.
--
--   **Formalization Note** The constants depend only on the fixed $F$. With $\log(eT)$ every quantity is positive from $T=1$, so the two-sided bounds hold for all $T\ge 1$.
--
--   Differences from the source:
--   - reading: L_F(T) = Θ(log(eT)), R*_F(T) ≍ R^LP_F(T) ≍ (log(eT))² → ∃ c, C > 0 with the six two-sided bounds for every T ≥ 1; reason: constants depend on the fixed F only (App. E.1.1); with log(eT) all quantities are positive from T = 1, so no threshold is needed
--   - encoding: F induces a bounded continuous proper loss → canonLoss FE8 is IsProperLoss, HasFiniteBayesRisk, has bayesPot = pot2 FE8 on Δ₂, |ℓ| ≤ B on Δ₂, and each ℓ(·, y) is ContinuousOn Δ₂ (EReal topology); reason: the induced loss is the canonical loss of App. E.1.1; the loss is real-valued, so EReal continuity is real continuity
--   - encoding: F(1/2) = 0 (continuous extension) → FE8 with an explicit case split at 1/2; reason: avoids relying on Real.log of e/0
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Theorem E.8, p.46 (= Theorem 1.16, p.9)

import Mathlib
import Definitions.Def_UCalibDirichlet_IsProperLoss
import Definitions.Def_UCalibDirichlet_HasFiniteBayesRisk
import Definitions.Def_UCalibDirichlet_bayesPot
import Definitions.Def_UCalibDirichlet_LF
import Definitions.Def_UCalibDirichlet_Supplement_pot2
import Definitions.Def_UCalibDirichlet_Supplement_canonLoss
import Definitions.Def_UCalibDirichlet_Supplement_lapRegret
import Definitions.Def_UCalibDirichlet_Supplement_minimaxRegret
import Definitions.Def_UCalibDirichlet_Supplement_FE8

namespace UCalibDirichlet.Supplement

/-- **Theorem E.8 (A logarithmic gap in the i.i.d. lower bound) = Theorem 1.16.** Frongillo, Luo,
Mehta & Schneider (manuscript, STOC 2027 submission), Theorem E.8, p.46: "Let
`F(p) = (p − 1/2)² log(e/|p − 1/2|)`, `F(1/2) = 0`. Then `F` induces a bounded continuous proper
loss, and `L_F(T) = Θ(log(eT))`, `R*_F(T) ≍ R^LP_F(T) ≍ (log(eT))²`." Its introduction version is
Theorem 1.16, p.9.

With `F = FE8` and its canonical loss `ℓ_F`:
1. `ℓ_F` is a proper loss with finite Bayes risk and potential `F`, it is bounded on `Δ₂`, and each
   `ℓ_F(·, y)` is continuous on `Δ₂`;
2. there are `c, C > 0` such that for every `T ≥ 1`:
   `c log(eT) ≤ L_F(T) ≤ C log(eT)`, `c (log eT)² ≤ R*_F(T) ≤ C (log eT)²` and
   `c (log eT)² ≤ R^LP_F(T) ≤ C (log eT)²`.

**Formalization Note.** `Θ` and `≍` hide constants depending on the fixed `F` only (App. E.1.1);
with `log(eT)` every quantity is positive from `T = 1`, so the bounds are stated for all `T ≥ 1`.
"Induces a proper loss" is the canonical loss `canonLoss FE8` with Bayes potential `pot2 FE8`.
Boundedness is a real bound `B` on `|ℓ_F|` over `Δ₂`; continuity is in the `EReal` topology on the
values (the loss is real-valued). -/
theorem theorem_E_8 :
    (IsProperLoss (canonLoss FE8) ∧ HasFiniteBayesRisk (canonLoss FE8) ∧
      (∀ q ∈ stdSimplex ℝ (Fin 2), bayesPot (canonLoss FE8) q = pot2 FE8 q) ∧
      (∃ B : ℝ, ∀ q ∈ stdSimplex ℝ (Fin 2), ∀ y : Fin 2,
        canonLoss FE8 q y ≤ (B : EReal) ∧ ((-B : ℝ) : EReal) ≤ canonLoss FE8 q y) ∧
      ∀ y : Fin 2, ContinuousOn (fun q => canonLoss FE8 q y) (stdSimplex ℝ (Fin 2))) ∧
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ T : ℕ, 1 ≤ T →
      c * Real.log (Real.exp 1 * T) ≤ LF (pot2 FE8) T ∧
      LF (pot2 FE8) T ≤ C * Real.log (Real.exp 1 * T) ∧
      ((c * Real.log (Real.exp 1 * T) ^ 2 : ℝ) : EReal) ≤ minimaxRegret (canonLoss FE8) T ∧
      minimaxRegret (canonLoss FE8) T ≤ ((C * Real.log (Real.exp 1 * T) ^ 2 : ℝ) : EReal) ∧
      ((c * Real.log (Real.exp 1 * T) ^ 2 : ℝ) : EReal) ≤ lapRegret (canonLoss FE8) T ∧
      lapRegret (canonLoss FE8) T ≤ ((C * Real.log (Real.exp 1 * T) ^ 2 : ℝ) : EReal) := by sorry

end UCalibDirichlet.Supplement
