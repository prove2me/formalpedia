-- Prove2me | Theorems.Thm_RobustBoolPCSP_Supplement_theorem_5_3
-- name    : RobustBoolPCSP.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:31:54.935194+00:00
-- url     : https://prove2.me/theorems/236834ea-d2af-457b-a92b-4e93074c4153
-- title:
--   Theorem 5.3 (Log-free local estimate) — $\Pr[\arg\max S\notin W]\le C_{P,W}(t+\sqrt\delta+\delta/t)$
-- statement:
--   Let $(P,W)$ be a pair of relations of arity $r$ on a finite set $A$ with the mode property. Let $\lambda$ be any probability distribution on $A^r$, $\delta=\lambda(A^r\setminus P)$, $Z_x\sim N(0,\lambda_x)$ independent ($Z_x=0$ if $\lambda_x=0$), and $S_{i,a}=p_{i,a}+t\sum_{x:x_i=a}Z_x$ with $0<t\le1$. Round each coordinate $i$ to a label of maximal score $S_{i,\cdot}$. Then there is a finite constant $C_{P,W}$ such that
--
--   $$\Pr[\arg\max S\notin W]\le C_{P,W}\Big(t+\sqrt\delta+\frac\delta t\Big)\qquad(0<t\le1).$$
--
--   The constant is uniform over $\lambda$ (including zero entries and arbitrarily small marginals) and over all deterministic tie-breaking rules.
--
--   This is the local estimate that removes the logarithmic factor in the square-root robustness bound.
--
--   Differences from the source:
--   - generalization: argmax rounding of each coordinate with any fixed deterministic tie-breaking rule → any map ρ from score matrices to tuples whose i-th output is a label of maximal score in row i (ties may be broken using the whole score matrix; no measurability assumed, the failure probability of a non-measurable event being its outer measure); reason: every fixed tie rule is such a map; the proof bounds, for each forbidden b, the event that every b_i is a maximal label of row i, which contains {ρ(S) = b} for every such map (pp.30–31)
--   - encoding: Gaussians Z_x ∼ N(0, λ_x), Z_x = 0 if λ_x = 0 → product of gaussianReal 0 λ_x; reason: Mathlib's Gaussian with variance 0 is the Dirac mass at 0
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), Theorem 5.3, p.29

import Mathlib
import Definitions.Def_RobustBoolPCSP_ModeProperty
import Definitions.Def_RobustBoolPCSP_Supplement_GaussRounding

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RobustBoolPCSP.Supplement

open RobustBoolPCSP

/-- **Theorem 5.3 (Log-free local estimate)**, p.29. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
Setting (p.29): "Let λ = (λ_x)_{x∈A^r} be a probability distribution, not necessarily supported on P,
and set δ = λ(A^r \ P). Let Z_x be independent centered Gaussians of variance λ_x, with Z_x = 0
whenever λ_x = 0. For 0 < t ≤ 1, define p_{i,a} = Σ_{x:x_i=a} λ_x, S_{i,a} = p_{i,a} + t Σ_{x:x_i=a} Z_x.
(17) Round coordinate i to a label maximizing its score, with any fixed deterministic tie-breaking
rule." Theorem: "If (P, W) has the mode property, there is a finite constant C_{P,W} such that
P[arg max S ∉ W] ≤ C_{P,W} (t + √δ + δ/t) (0 < t ≤ 1). (18) The constant is uniform over λ, including
distributions with zero entries or arbitrarily small marginals, and over all deterministic
tie-breaking rules."

**Formalization Note.** The law of `(Z_x)_x` is `gaussLaw λ`, the scores are `score λ t` and
`δ = defect P λ`. A rounding rule is any map `ρ` from score matrices `S = (S_{i,a})` to tuples whose
`i`-th output is a label of maximal score in row `i`; its tie-breaking may depend on the whole
score matrix, and no measurability is assumed (the probability of a non-measurable failure event
is its outer measure under `gaussLaw λ`). This contains every fixed deterministic tie-breaking rule.
The constant `C` is chosen after `(P, W)` and before the rule, `λ` and `t`. -/
theorem theorem_5_3 {A : Type} [Fintype A] [DecidableEq A] [Nonempty A] {r : ℕ}
    (P W : Set (Fin r → A)) (hmode : ModeProperty P W) :
    ∃ C : ℝ, ∀ ρ : (Fin r → A → ℝ) → Fin r → A,
      (∀ (z : Fin r → A → ℝ) (i : Fin r) (a : A), z i a ≤ z i (ρ z i)) →
      ∀ lam : (Fin r → A) → ℝ≥0, ∑ x, (lam x : ℝ) = 1 → ∀ t : ℝ, 0 < t → t ≤ 1 →
        gaussLaw lam {z | ρ (score lam t z) ∉ W} ≤
          ENNReal.ofReal (C * (t + Real.sqrt (defect P lam) + defect P lam / t)) := by sorry

end RobustBoolPCSP.Supplement
