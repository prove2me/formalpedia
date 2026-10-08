-- Prove2me | Theorems.Thm_RobustPower_SimplexGap_theorem_2_6_simplex_gap
-- name    : RobustPower.SimplexGap.theorem_2_6_simplex_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:30:09.057338+00:00
-- url     : https://prove2.me/theorems/4b79317e-e6fc-43d1-aeb1-6c870db0134b
-- title:
--   Theorem 2.6 — on the uniform corner simplex, z_Rob(b) ≥ (n + 1) · z_Stoch(b)
-- statement:
--   Consider the two-stage problems $\Pi_{\mathrm{Rob}}(b)$ (1.2) and $\Pi_{\mathrm{Stoch}}(b)$ (1.1) on the following instance:
--
--   1. no first stage: $n_1=0$, $A=0$, $c=0$;
--   2. $n_2=m=n\ge 3$, $B=I_n$ (the $n\times n$ identity), and $d=e_n=(0,\dots,0,1)$;
--   3. continuous second-stage variables ($p_2=0$, so $y\ge 0$ with no integrality);
--   4. the uncertainty set is the corner simplex (2.29)
--   $$I_b(\Omega)=\Big\{\,b \;:\; \sum_{j=1}^n b_j\le 1,\ b\ge 0\,\Big\};$$
--   5. $\mu$ is the uniform probability measure on $I_b(\Omega)$: the law of $b(\omega)$ under $\mu$ is Lebesgue measure on $I_b(\Omega)$ divided by $\operatorname{vol}(I_b(\Omega))$.
--
--   Then
--   $$z_{\mathrm{Rob}}(b)\ \ge\ (n+1)\cdot z_{\mathrm{Stoch}}(b).$$
--
--   Since $I_b(\Omega)$ is not symmetric (Lemma 2.4), this shows that the symmetry hypothesis of the paper's bound $z_{\mathrm{Rob}}(b)\le 2\,z_{\mathrm{Stoch}}(b)$ cannot be dropped: without it the stochasticity gap is unbounded as $n\to\infty$.
--
--   **Formalization Note** The statement quantifies over every scenario model $(\Omega,\mu,b)$ with $\mu$ a probability measure, $b$ measurable, range of $b$ equal to the simplex, and law of $b$ equal to normalized Lebesgue measure on it (for example $\Omega$ the simplex and $b$ the identity). Both optimal values are `EReal` infima, so an infeasible stochastic problem would give $+\infty$ and the inequality would fail; the multiplication is in `EReal`. Policies of $\Pi_{\mathrm{Stoch}}(b)$ are integrable and feasible in every scenario. The hypothesis $n\ge 3$ is the paper's; the argument does not appear to need more than $n\ge 1$.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 19, Theorem 2.6 (proof p. 20)

import Mathlib
import Definitions.Def_RobustPower_SimplexGap_Problems
import Definitions.Def_RobustPower_SimplexGap_SimplexInstance

namespace RobustPower.SimplexGap

open MeasureTheory

/-- Theorem 2.6: on the instance `n₁ = 0`, `n₂ = m = n ≥ 3`, `A = 0`, `c = 0`, `d = eₙ`,
`B = Iₙ`, with uncertainty set the corner simplex (2.29) and `μ` the uniform probability measure on
it, `z_Rob(b) ≥ (n + 1) · z_Stoch(b)`. -/
theorem theorem_2_6_simplex_gap (n : ℕ) (hn : 3 ≤ n) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → Fin n → ℝ)
    (hμb : IsUniformOnSimplex n μ b) :
    ((((n : ℝ) + 1 : ℝ) : EReal) *
        zStoch μ (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Fin 0 → ℝ)
          (lastUnit n) b ∅ ∅) ≤
      zRob (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Fin 0 → ℝ)
        (lastUnit n) b ∅ ∅ := by sorry

end RobustPower.SimplexGap
