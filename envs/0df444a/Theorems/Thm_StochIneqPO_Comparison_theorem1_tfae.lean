-- Prove2me | Theorems.Thm_StochIneqPO_Comparison_theorem1_tfae
-- name    : StochIneqPO.Comparison.theorem1_tfae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:18:29.435965+00:00
-- url     : https://prove2.me/theorems/8582dc5b-8e58-49ad-a20c-4d302993cc8a
-- title:
--   Theorem 1 — six equivalent characterizations of $P_1 \prec P_2$ (Strassen)
-- statement:
--   Let $E$ be a partially ordered Polish space: a Polish space with a closed partial order $\le$ and its Borel $\sigma$-algebra. Let $P_1, P_2$ be probability measures on $E$. The following six conditions are equivalent.
--
--   1. $P_1 \prec P_2$.
--   2. There is a probability measure $\lambda$ on $E \times E$ with support in $K = \{(x,y) : x \le y\}$, first marginal $P_1$ and second marginal $P_2$.
--   3. There are a real random variable $Z$ (on some probability space) and measurable maps $f, g : \mathbb R \to E$ with $f(t) \le g(t)$ for all $t$, such that $f(Z)$ has law $P_1$ and $g(Z)$ has law $P_2$.
--   4. There are $E$-valued random variables $X_1, X_2$ on a common probability space with $X_1 \le X_2$ almost surely and $X_i \sim P_i$ ($i = 1, 2$).
--   5. There is an upward stochastic kernel $k$ on $E \times E$ with $P_2 = P_1^{k}$, the second marginal of $P_1 * k$.
--   6. $P_1(B) \le P_2(B)$ for every closed increasing set $B \subseteq E$.
--
--   The equivalence (i) $\Leftrightarrow$ (iv) is the monotone coupling characterization of the stochastic order; (i) $\Rightarrow$ (ii) is a special case of Strassen's theorem (1965). Every comparison result of the paper reduces to this theorem. The platform item `PalmQueueing.Ordering.strassen_st` is the special case (i) $\Leftrightarrow$ (iv) for $E = \mathbb R^n$ with the coordinatewise order.
--
--   **Formalization Note** "Partially ordered Polish space" is `[PolishSpace E] [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]` (the order's graph is closed). Random variables live on some probability space `Ω : Type`. "Support in $K$" is $\lambda(K^{\mathrm c}) = 0$; "$f \le g$" is pointwise on all of $\mathbb R$; $P_1^k$ is `(P₁ ⊗ₘ k).snd`; the kernel in (v) is a Markov kernel. A closed set is Borel, so (vi) needs no separate measurability hypothesis.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Theorem 1, p. 900 (PDF p. 2)

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Definitions.Def_StochIneqPO_Comparison_IsUpward

namespace StochIneqPO.Comparison

open MeasureTheory ProbabilityTheory

theorem theorem1_tfae {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E]
    [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]
    (P₁ P₂ : Measure E) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] :
    List.TFAE
      [ -- (i)
        StochLE P₁ P₂,
        -- (ii)
        ∃ lam : Measure (E × E), IsProbabilityMeasure lam ∧ lam {z : E × E | z.1 ≤ z.2}ᶜ = 0 ∧
          lam.map Prod.fst = P₁ ∧ lam.map Prod.snd = P₂,
        -- (iii)
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
          ∃ (Z : Ω → ℝ) (f g : ℝ → E), Measurable Z ∧ Measurable f ∧ Measurable g ∧
            (∀ t, f t ≤ g t) ∧ μ.map (fun ω => f (Z ω)) = P₁ ∧ μ.map (fun ω => g (Z ω)) = P₂,
        -- (iv)
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
          ∃ X₁ X₂ : Ω → E, Measurable X₁ ∧ Measurable X₂ ∧ (∀ᵐ ω ∂μ, X₁ ω ≤ X₂ ω) ∧
            μ.map X₁ = P₁ ∧ μ.map X₂ = P₂,
        -- (v)
        ∃ k : Kernel E E, IsMarkovKernel k ∧ IsUpward k ∧ P₂ = (P₁ ⊗ₘ k).snd,
        -- (vi)
        ∀ B : Set E, IsClosed B → IsUpperSet B → P₁ B ≤ P₂ B ] := by sorry

end StochIneqPO.Comparison
