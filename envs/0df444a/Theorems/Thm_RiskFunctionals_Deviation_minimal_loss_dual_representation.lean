-- Prove2me | Theorems.Thm_RiskFunctionals_Deviation_minimal_loss_dual_representation
-- name    : RiskFunctionals.Deviation.minimal_loss_dual_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:49.263367+00:00
-- url     : https://prove2.me/theorems/e2abf455-0606-4d52-b78d-e0a661d77ccd
-- title:
--   Theorem 2.75 — dual representation of minimal loss functionals, $\mathcal D(Y)=\sup\{\mathbb E(YZ)-\mathbb Eh^*(Z) : \mathbb EZ=0\}$, and of $\mathbb E-\mathcal D$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $1\le p<\infty$, and $q$ the conjugate exponent, $1/p+1/q=1$; random variables $Y$ lie in $L_p$ and dual variables $Z$ in $L_q$. Let $h$ be a non-negative convex function on $\mathbb R$ with $h(0)=0$, let $h^*(v)=\sup\{uv-h(u) : u\in\mathbb R\}$ be its Fenchel conjugate, and let
--   $$\mathcal D(Y)=\min\{\mathbb E[h(Y-a)] : a\in\mathbb R\}$$
--   be the minimal loss functional of $h$, for $Y$ such that $\mathbb E[h(Y)]$ exists. For $0<\alpha\le1$, $\mathbb{AV@R}_\alpha(Y)=\frac1\alpha\int_0^\alpha G^{-1}(u)\,du$ is the average value-at-risk and $\mathbb{AV@R}\mathbb D_\alpha(Y)=\mathbb E(Y)-\mathbb{AV@R}_\alpha(Y)$ its deviation.
--
--   1. $\mathcal D$ has the dual representation
--   $$\mathcal D(Y)=\sup\{\mathbb E(YZ)-\mathbb Eh^*(Z) : \mathbb EZ=0\}. \tag{2.113}$$
--   2. In particular,
--   $$\mathbb{AV@R}\mathbb D_\alpha(Y)=\sup\Big\{\mathbb E(YZ) : -\frac{1-\alpha}{\alpha}\le Z\le1,\ \mathbb EZ=0\Big\}. \tag{2.114}$$
--   3. $\mathbb EY-\mathcal D(Y)$ has the dual representation
--   $$\mathcal A(Y):=\mathbb EY-\mathcal D(Y)=\inf\{\mathbb E(YZ)+\mathbb E[h^*(1-Z)] : \mathbb E(Z)=1\}.$$
--   4. In particular (compare (2.20)),
--   $$\mathbb{AV@R}_\alpha(Y)=\min\Big\{\mathbb E(YZ) : \mathbb EZ=1,\ 0\le Z\le\frac1\alpha\Big\}.$$
--
--   The theorem turns every minimal loss deviation functional, and the acceptability functional $\mathbb E-\mathcal D$, into a supremum (infimum) of linear functionals of $Y$ over an explicit set of dual variables, which is what makes these functionals usable as risk measures in optimization.
--
--   **Formalization Note** $\mathcal D(Y)$ is the **infimum** over $a$ of $\mathbb E[h(Y-a)]$, a value in $[0,+\infty]$ (the book's "min" presupposes attainment, which fails e.g. for $h(v)=[v]^+$ and unbounded $Y$; attainment is not claimed). Parts 1 and 3 assume $Y$ measurable, $Y\in L_p$ and $h(Y)$ integrable (the book's standing assumption of §2.5.5 that $\mathbb E[h(Y)]$ exists), so $\mathcal D(Y)$ is finite. $h^*$ is extended-real valued; the supremum in part 1 (infimum in part 3) is taken over the measurable $Z\in L_q$ with the stated mean for which $h^*(Z)$ (resp. $h^*(1-Z)$) is almost surely finite and integrable — the remaining $Z$ contribute $-\infty$ (resp. $+\infty$) in the book's formula and do not change it. Parts 2 and 4 assume $Y$ measurable and in $L_p$, $0<\alpha\le1$; the constraints on $Z$ hold almost surely, and the minimum in part 4 is stated as attained (`IsLeast`). Suprema and infima are taken in the extended reals.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, pp. 109–110, Theorem 2.75

import Mathlib
import Definitions.Def_RiskFunctionals_Deviation_AverageValueAtRisk
import Definitions.Def_RiskFunctionals_Deviation_MinimalLoss

namespace RiskFunctionals.Deviation

open MeasureTheory

/-- Theorem 2.75 (Pflug & Römisch, pp. 109–110), on `Y ∈ L_p`, `Z ∈ L_q`, `1 ≤ p < ∞`,
`1/p + 1/q = 1`. Let `h` be a non-negative convex function on `ℝ` with `h(0) = 0`, let
`𝒟(Y) = min {𝔼[h(Y − a)] : a ∈ ℝ}` (2.109) be the minimal loss functional (rendered as an
infimum, `minimalLoss`), and suppose `𝔼[h(Y)]` exists (§2.5.5). Let `h*` be the Fenchel
conjugate `h*(v) = sup {u v − h(u) : u ∈ ℝ}`.
(i) `𝒟(Y) = sup {𝔼(Y Z) − 𝔼h*(Z) : 𝔼Z = 0}` (2.113); in particular
`𝔸𝕍@ℝ𝔻_α(Y) = sup {𝔼(Y Z) : −(1 − α)/α ≤ Z ≤ 1, 𝔼Z = 0}` (2.114).
(ii) `𝒜(Y) := 𝔼Y − 𝒟(Y) = inf {𝔼(Y Z) + 𝔼[h*(1 − Z)] : 𝔼(Z) = 1}`; in particular
`𝔸𝕍@ℝ_α(Y) = min {𝔼(Y Z) : 𝔼Z = 1, 0 ≤ Z ≤ 1/α}`.
The suprema and infima range over the `Z` for which the conjugate term is finite (the other `Z`
contribute `−∞` to the supremum and `+∞` to the infimum). -/
theorem minimal_loss_dual_representation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [p.HolderConjugate q] :
    -- (i), (2.113)
    (∀ h : ℝ → ℝ, (∀ u, 0 ≤ h u) → ConvexOn ℝ Set.univ h → h 0 = 0 →
      ∀ Y : Ω → ℝ, Measurable Y → MemLp Y p P → Integrable (fun ω => h (Y ω)) P →
        ((minimalLoss P h Y : ENNReal) : EReal) =
          ⨆ Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧ ∫ ω, Z ω ∂P = 0 ∧
              HasFiniteExpectedConj P h Z},
            ((∫ ω, Y ω * Z ω ∂P - expectedConj P h Z : ℝ) : EReal)) ∧
    -- (i), (2.114)
    (∀ α : ℝ, 0 < α → α ≤ 1 → ∀ Y : Ω → ℝ, Measurable Y → MemLp Y p P →
      ((avarDeviation P Y α : ℝ) : EReal) =
        ⨆ Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧
            (∀ᵐ ω ∂P, -((1 - α) / α) ≤ Z ω ∧ Z ω ≤ 1) ∧ ∫ ω, Z ω ∂P = 0},
          ((∫ ω, Y ω * Z ω ∂P : ℝ) : EReal)) ∧
    -- (ii), the dual representation of `𝔼 − 𝒟`
    (∀ h : ℝ → ℝ, (∀ u, 0 ≤ h u) → ConvexOn ℝ Set.univ h → h 0 = 0 →
      ∀ Y : Ω → ℝ, Measurable Y → MemLp Y p P → Integrable (fun ω => h (Y ω)) P →
        ((∫ ω, Y ω ∂P : ℝ) : EReal) - ((minimalLoss P h Y : ENNReal) : EReal) =
          ⨅ Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧ ∫ ω, Z ω ∂P = 1 ∧
              HasFiniteExpectedConj P h (fun ω => 1 - Z ω)},
            ((∫ ω, Y ω * Z ω ∂P + expectedConj P h (fun ω => 1 - Z ω) : ℝ) : EReal)) ∧
    -- (ii), the representation of `𝔸𝕍@ℝ_α`, with attainment
    (∀ α : ℝ, 0 < α → α ≤ 1 → ∀ Y : Ω → ℝ, Measurable Y → MemLp Y p P →
      IsLeast {v : ℝ | ∃ Z : Ω → ℝ, Measurable Z ∧ MemLp Z q P ∧ ∫ ω, Z ω ∂P = 1 ∧
          (∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ 1 / α) ∧ v = ∫ ω, Y ω * Z ω ∂P}
        (averageValueAtRisk P Y α)) := by sorry

end RiskFunctionals.Deviation
