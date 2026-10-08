-- Prove2me | Theorems.Thm_PoissonDirichlet_Ratio_proposition_10_iii
-- name    : PoissonDirichlet.Ratio.proposition_10_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:07.512278+00:00
-- url     : https://prove2.me/theorems/b0ab66ee-b505-4b21-9ebe-c1069361ac50
-- title:
--   Proposition 10 (iii): Poisson arrival times and normalized powers
-- statement:
--   Let $(V_n)$ have $\mathrm{PD}(\alpha,0)$ law for $0<\alpha<1$, and let $L=\lim_n nV_n^\alpha$ be the local time. For $C>0$ set $\Sigma=(L/C)^{-1/\alpha}$, $\Delta_n=V_n\Sigma$, and $X_n=C\Delta_n^{-\alpha}=LV_n^{-\alpha}$. Then $0<X_1<X_2<\cdots$, the sequence $(X_n)$ has the joint law of the cumulative sums of independent standard exponential variables, and
--
--   $$
--   V_n=\frac{X_n^{-1/\alpha}}{\sum_{m\geq1}X_m^{-1/\alpha}}.
--   $$
--
--   This representation supplies the Poisson arrival time input used in the proof of Proposition 8.
--
--   **Formalization Note** The joint law is equality of probabilities of every measurable set of sequences; $X_{k+1}$ is Lean's `X ω k`. The page's "points of a PRM$(dx)$ on $(0,\infty)$" is encoded by its own gloss (28): the law of the partial sums of independent standard exponential variables, taken on any probability space carrying such a sequence.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 862, Proposition 10 (iii), (27)–(29)

import Mathlib
import Definitions.Def_PoissonDirichlet_Ratio_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Ratio

/-- Proposition 10 (iii), equations (27)–(29). The joint law of the arrival
times is expressed through any sequence of independent Exp(1) variables. -/
theorem proposition_10_iii {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (V : Ω → ℕ → ℝ) (hV : HasPD α 0 P V)
    (L : Ω → ℝ)
    (hL : ∀ᵐ ω ∂P, Tendsto
      (fun k : ℕ => ((k : ℝ) + 1) * (V ω k) ^ α)
      atTop (𝓝 (L ω)))
    (C : ℝ) (hC : 0 < C) :
    let X : Ω → ℕ → ℝ := fun ω k => L ω * (V ω k) ^ (-α)
    (∀ᵐ ω ∂P, ∀ k : ℕ,
      0 < X ω k ∧ X ω k < X ω (k + 1) ∧
        X ω k = C * (V ω k * (L ω / C) ^ (-1 / α)) ^ (-α)) ∧
    (∀ {Ω' : Type*} [MeasurableSpace Ω']
      (Q : Measure Ω') [IsProbabilityMeasure Q]
      (ε : ℕ → Ω' → ℝ),
      iIndepFun ε Q →
      (∀ i : ℕ, HasLaw (ε i) (expMeasure 1) Q) →
      ∀ s : Set (ℕ → ℝ), MeasurableSet s →
        P ((fun ω k => X ω k) ⁻¹' s) =
          Q ((fun ω k => ∑ i ∈ Finset.range (k + 1), ε i ω) ⁻¹' s)) ∧
    (∀ᵐ ω ∂P, ∀ k : ℕ,
      V ω k = (X ω k) ^ (-1 / α) /
        ∑' m : ℕ, (X ω m) ^ (-1 / α)) := by sorry

end PoissonDirichlet.Ratio
