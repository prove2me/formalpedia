-- Prove2me | Theorems.Thm_RiskFunctionals_Deviation_integral_conjugate_duality
-- name    : RiskFunctionals.Deviation.integral_conjugate_duality
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:49.043634+00:00
-- url     : https://prove2.me/theorems/68de106a-e2dc-4f71-b64f-da11b38dd58e
-- title:
--   Proposition B.3 — $\mathbb E[h(V)]=\sup\{\mathbb E(VZ)-\mathbb E(h^*(Z)) : \mathbb E(h^*(Z))<\infty\}$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $1\le p<\infty$ and $q$ its conjugate exponent, $1/p+1/q=1$. Let $h:\mathbb R\to\mathbb R$ be a real valued, convex, lower semicontinuous function whose Fenchel conjugate $h^*(v)=\sup_u\{uv-h(u)\}$ is non-negative: $h^*(v)\ge0$ for all $v$. Then for every $V\in L_p(\Omega,\mathcal F,\mathbb P)$,
--   $$\mathbb E[h(V)]=\sup\{\mathbb E(VZ)-\mathbb E(h^*(Z)) : \mathbb E(h^*(Z))<\infty\},$$
--   the supremum taken over $Z\in L_q$.
--
--   The expectation $\mathbb E[h(V)]$ always exists in $(-\infty,+\infty]$; the statement has two parts:
--   1. if $h(V)$ is integrable, its expectation equals the supremum;
--   2. if $h(V)$ is not integrable, the supremum is $+\infty$.
--
--   This is the conjugacy of the integral functional $V\mapsto\mathbb E[h(V)]$ on $L_p$ with $Z\mapsto\mathbb E[h^*(Z)]$ on $L_q$, the infinite-dimensional ingredient of the dual representation of minimal loss functionals.
--
--   **Formalization Note** $V$ and $Z$ are measurable real functions with $V\in L_p$, $Z\in L_q$ (`MemLp`), $p<\infty$. "$\mathbb E(h^*(Z))<\infty$" means that $h^*(Z)$ is almost surely finite and integrable, and $\mathbb E(h^*(Z))$ is then its integral. The supremum is taken in the extended reals. The book writes the left side with a roman $E$ and does not spell out the non-integrable case; the second part says what "$\mathbb E[h(V)]=+\infty$" means there.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 272, Proposition B.3

import Mathlib
import Definitions.Def_RiskFunctionals_Deviation_MinimalLoss

namespace RiskFunctionals.Deviation

open MeasureTheory

/-- Proposition B.3 (Pflug & Römisch, p. 272): let `h` be a real valued convex l.s.c. function
whose dual function `h*` is non-negative. Then for `V ∈ L_p`,
`𝔼[h(V)] = sup {𝔼(V Z) − 𝔼(h*(Z)) : 𝔼(h*(Z)) < ∞}`, the supremum over `Z ∈ L_q`,
`1/p + 1/q = 1`, `1 ≤ p < ∞`. `𝔼[h(V)]` lies in `(−∞, +∞]`: when `h(V)` is integrable the
supremum is its expectation, and otherwise the supremum is `+∞`. -/
theorem integral_conjugate_duality {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [p.HolderConjugate q] (h : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ h)
    (hlsc : LowerSemicontinuous h) (hconj : ∀ v : ℝ, 0 ≤ fenchelConj h v)
    (V : Ω → ℝ) (hV : Measurable V) (hVp : MemLp V p P) :
    (Integrable (fun ω => h (V ω)) P →
      ((∫ ω, h (V ω) ∂P : ℝ) : EReal) =
        ⨆ Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧ HasFiniteExpectedConj P h Z},
          ((∫ ω, V ω * Z ω ∂P - expectedConj P h Z : ℝ) : EReal)) ∧
    (¬ Integrable (fun ω => h (V ω)) P →
      ⨆ Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧ HasFiniteExpectedConj P h Z},
          ((∫ ω, V ω * Z ω ∂P - expectedConj P h Z : ℝ) : EReal) = ⊤) := by sorry

end RiskFunctionals.Deviation
