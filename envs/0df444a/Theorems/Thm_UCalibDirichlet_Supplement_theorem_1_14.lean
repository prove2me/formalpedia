-- Prove2me | Theorems.Thm_UCalibDirichlet_Supplement_theorem_1_14
-- name    : UCalibDirichlet.Supplement.theorem_1_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:13:52.094334+00:00
-- url     : https://prove2.me/theorems/14d20e67-65ae-4323-85dd-2b6709ca1982
-- title:
--   Theorem 1.14 — sharp binary regret under regular variation: $R^*_F(T)=\Theta(L_F(T))$ and $\mathrm{Reg}_F(T)=O(L_F(T))$
-- statement:
--   Let $K=2$ and let $F:[0,1]\to\mathbb R$ be a convex potential such that $F'$ is absolutely continuous on $[0,1]$ and $F''$ is bounded near $0$ and $1$. Let $A$ be a sequence that is regularly varying with index $\rho>0$, and suppose $L_F(T)\asymp A(T)$, i.e. $a\,A(T)\le L_F(T)\le b\,A(T)$ for all sufficiently large $T$, with constants $a,b>0$. (In particular one may take $A=L_F$ when $L_F$ itself is regularly varying with index $\rho>0$.) Here
--   $$L_F(T)=T\sup_{p\in[0,1]}\Big\{\mathbb E_{S\sim\mathrm{Bin}(T,p)}F(S/T)-F(p)\Big\}.$$
--   Then, for the canonical loss $\ell_F(p,y)=-F(p)-F'(p)(y-p)$, there are constants $c,C>0$ and $T_0$ such that for all $T\ge T_0$
--   $$c\,L_F(T)\ \le\ R^*_F(T)\ \le\ C\,L_F(T)\qquad\text{and}\qquad R^{\mathrm{LP}}_F(T)\ \le\ C\,L_F(T),$$
--   where $R^*_F$ is the minimax regret and $R^{\mathrm{LP}}_F$ the worst-case expected regret of Algorithm 1 (the Laplace forecaster).
--
--   The Bernstein gap $L_F$ is always a lower bound on the minimax regret; under regular variation it is also, up to a constant, the regret of Algorithm 1, so Algorithm 1 is minimax optimal for such losses.
--
--   **Formalization Note** $\Theta$, $O$ and $\asymp$ are asymptotic in $T$, with constants allowed to depend on $F$ and $A$ but not on $T$ (the convention of Appendix E.1.1).
--
--   Differences from the source:
--   - reading: R*_F(T) = Θ(L_F(T)), Reg_F(T) = O(L_F(T)), L_F(T) ≍ A(T) → ∃ c, C > 0 and T₀ with the bounds for all T ≥ T₀; L_F ≍ A as a, b > 0 and a threshold; reason: asymptotic notation with constants depending on F and A, not on T (App. E.1.1, p.40)
--   - reading: F (convexity not repeated in the theorem's sentence) → hypothesis ConvexOn ℝ [0,1] F; reason: standing assumption: F is the convex potential of a proper loss, and App. E's statements concern finite continuous convex potentials (p.40)
--   - encoding: F′ absolutely continuous on [0,1], F″ bounded near 0 and 1 → ACDerivBddEnds F: F differentiable within [0,1], derivWithin F [0,1] absolutely continuous, |deriv F′| ≤ M a.e. on [0,η] ∪ [1−η,1]; reason: the hypothesis presupposes F′ on [0,1]; curvature bounds are a.e. (App. E.1.1)
--   - encoding: Reg_F(T) of Algorithm 1, R*_F(T), binary forecasts p ∈ [0,1] → lapRegret (canonLoss F) T, minimaxRegret (canonLoss F) T, forecasts q ∈ Δ₂ with p = q 1, L_F = LF (pot2 F); reason: the canonical loss of App. E.1.1 and the base model at K = 2
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Theorem 1.14, p.8 (proved as Corollary E.2, p.41)

import Mathlib
import Definitions.Def_UCalibDirichlet_LF
import Definitions.Def_UCalibDirichlet_Supplement_pot2
import Definitions.Def_UCalibDirichlet_Supplement_canonLoss
import Definitions.Def_UCalibDirichlet_Supplement_lapRegret
import Definitions.Def_UCalibDirichlet_Supplement_minimaxRegret
import Definitions.Def_UCalibDirichlet_Supplement_IsRegVarSeq
import Definitions.Def_UCalibDirichlet_Supplement_ACDerivBddEnds

namespace UCalibDirichlet.Supplement

/-- **Theorem 1.14 (Sharp regret under regular variation).** Frongillo, Luo, Mehta & Schneider
(manuscript, STOC 2027 submission), Theorem 1.14, p.8: "Suppose `F′` is absolutely continuous on
`[0, 1]`, `F″` is bounded near 0 and 1, and `L_F` is regularly varying with index `ρ > 0`. Then
`R*_F(T) = Θ(L_F(T))`, `Reg_F(T) = O(L_F(T))`. More generally, it suffices that `L_F(T) ≍ A(T)` for
some `A` regularly varying with index `ρ > 0`." (Proved as Corollary E.2, p.41.)

For a binary (`K = 2`) convex potential `F` satisfying `ACDerivBddEnds F`, and a sequence `A`
regularly varying with index `ρ > 0` with `a A(T) ≤ L_F(T) ≤ b A(T)` for all large `T`
(`a, b > 0`), there are `c, C > 0` and `T₀` such that for every `T ≥ T₀`, with the canonical loss
`ℓ_F`:
`c L_F(T) ≤ R*_F(T) ≤ C L_F(T)` and `R^LP_F(T) ≤ C L_F(T)`.

**Formalization Note.** The statement is the "more generally" form, which contains the first one
(`A = L_F`, `a = b = 1`). `Θ`, `O` and `≍` are asymptotic in `T` with constants that may depend on
`F` and `A` but not on `T` (App. E.1.1, p.40). Convexity of `F` on `[0, 1]` is the standing
assumption of App. E ("finite continuous convex potentials", p.40). `L_F` is the binary (60), i.e.
the base `LF (pot2 F)`; `Reg_F(T)` of Algorithm 1 is the worst case over sequences, `lapRegret`. -/
theorem theorem_1_14 (F : ℝ → ℝ) (hconv : ConvexOn ℝ (Set.Icc 0 1) F) (hF : ACDerivBddEnds F)
    (A : ℕ → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (hA : IsRegVarSeq A ρ)
    (hLA : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
      a * A T ≤ LF (pot2 F) T ∧ LF (pot2 F) T ≤ b * A T) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
      ((c * LF (pot2 F) T : ℝ) : EReal) ≤ minimaxRegret (canonLoss F) T ∧
        minimaxRegret (canonLoss F) T ≤ ((C * LF (pot2 F) T : ℝ) : EReal) ∧
        lapRegret (canonLoss F) T ≤ ((C * LF (pot2 F) T : ℝ) : EReal) := by sorry

end UCalibDirichlet.Supplement
