-- Prove2me | Theorems.Thm_SupermodDRO_proposition_1
-- name    : SupermodDRO.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:28.52947+00:00
-- url     : https://prove2.me/theorems/03af57ec-9475-456f-9dc2-80aeee9472c9
-- title:
--   Proposition 1, p.8 — a worst case over $\mathcal F^k$ with three-point marginals (5)
-- statement:
--   Fix a scenario with data $(\mu,\delta,\underline z,\overline z)$ satisfying the assumptions of p.7, and a first-stage decision $x$ with $g(x,\cdot)>-\infty$. There is a distribution $\mathbb P^*\in\mathcal F^k$ attaining
--   $$
--   \mathbb E_{\mathbb P^*}[g(x,\tilde z)]=\sup_{\mathbb P\in\mathcal F^k}\mathbb E_{\mathbb P}[g(x,\tilde z)]
--   $$
--   whose marginals are, for every coordinate $i$ with $\underline z_i<\overline z_i$ and $\hat\delta_i=\min\{\delta_i,\,2(\overline z_i-\mu_i)(\mu_i-\underline z_i)/(\overline z_i-\underline z_i)\}$,
--   $$
--   \mathbb P^*(\tilde z_i=w)=\begin{cases}
--   \dfrac{\hat\delta_i}{2(\mu_i-\underline z_i)} & w=\underline z_i,\\[4pt]
--   1-\dfrac{\hat\delta_i(\overline z_i-\underline z_i)}{2(\overline z_i-\mu_i)(\mu_i-\underline z_i)} & w=\mu_i,\\[4pt]
--   \dfrac{\hat\delta_i}{2(\overline z_i-\mu_i)} & w=\overline z_i,\\[4pt]
--   0 & \text{otherwise,}
--   \end{cases}
--   $$
--   and $\mathbb P^*(\tilde z_i=\mu_i)=1$ for every coordinate with $\underline z_i=\overline z_i$.
--
--   The marginals do not depend on $x$; only the coupling between coordinates may. This reduces the worst case to distributions on the $3^n$ grid $\prod_i\{\underline z_i,\mu_i,\overline z_i\}$.
--
--   **Formalization Note** The hypothesis $g(x,\cdot)>-\infty$ is a consequence of the paper's standing assumption that Problem (2) has a finite value. Probabilities are compared as real numbers.
--
--   Differences from the source:
--   - generalization: standing assumption that Problem (2) has a finite optimal value → only its consequence g(x, ·) > −∞ is assumed; reason: the standing assumption implies g > −∞ everywhere, so the paper's setting is an instance
--   - reading: z̲ᵏ ≤ µᵏ ≤ z̄ᵏ and δᵏ ≥ 0 are never stated → assumed (in ScenarioAssumptions); reason: used throughout the paper: the support contains the mean, (5) is a probability vector, and p.7 treats µᵢᵏ ∈ {z̄ᵢᵏ, z̲ᵢᵏ} as the boundary case
--   - encoding: ℙ^{k*}(z̃ᵢ = w) as numbers, and the line 'otherwise' → (ℙ*{z | zᵢ = w}).toReal, and ℙ*{zᵢ ∉ {z̲ᵢ, µᵢ, z̄ᵢ}} = 0; reason: ℙ* is a probability measure; same content
--   - encoding: expectation of the [−∞, ∞]-valued g → extended expectation ∫g⁺ − ∫g⁻ in EReal, +∞ when ∫g⁺ = ∞; reason: the standard convention; it agrees with the paper whenever the expectation is defined
--   - encoding: g(x, z) = min b⊤y, with g(x, z) = ∞ if (1) is infeasible → the infimum in EReal: ⊤ on an empty feasible set, ⊥ on an unbounded program; reason: same value whenever (1) is infeasible or has an optimal value; the paper never writes the unbounded case
--   - encoding: [n] indexed from 1 → Fin n indexed from 0; reason: Lean convention; same instances
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), Proposition 1 and (5), p.8, with the remark after it

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_SupermodDRO_secondStageCost
import Definitions.Def_SupermodDRO_scenarioSet
import Definitions.Def_SupermodDRO_scenarioWorstCase
import Definitions.Def_SupermodDRO_ScenarioAssumptions
import Definitions.Def_SupermodDRO_levelMass

open MeasureTheory

namespace SupermodDRO

/-- **Proposition 1 (a worst case over `𝓕ᵏ` with three-point marginals (5)).** Long, Qi & Zhang,
*Supermodularity in Two-Stage Distributionally Robust Optimization*, author manuscript (June 2022),
Proposition 1, p.8: "For any x, there exists ℙ^{k*} ∈ arg sup_{ℙᵏ∈𝓕ᵏ} E_{ℙᵏ}[g(x, z̃)] such that for
all i ∈ [n], the marginal distribution is independent of x and can be calculated as (5) … where
δ̂ᵢᵏ = min{δᵢᵏ, 2(z̄ᵢᵏ − µᵢᵏ)(µᵢᵏ − z̲ᵢᵏ)/(z̄ᵢᵏ − z̲ᵢᵏ)} for all i ∈ [n] with z̄ᵢᵏ > z̲ᵢᵏ", with the remark
after it (p.8): "for i with z̄ᵢᵏ = z̲ᵢᵏ, obviously ℙ^{k*}(z̃ᵢ = z̄ᵢᵏ) = ℙ^{k*}(z̃ᵢ = µᵢᵏ) =
ℙ^{k*}(z̃ᵢ = z̲ᵢᵏ) = 1".

For one scenario with data `μ, δ, zl, zu` satisfying the assumptions of p.7 and every `x` with
`g(x, ·) > −∞`, some `P* ∈ 𝓕ᵏ` attains the supremum of `E_P[g(x, z̃)]` over `𝓕ᵏ`, and for every
coordinate `i`: if `zl i < zu i`, the marginal of `z̃ᵢ` under `P*` puts the masses
`δ̂ᵢ/(2(µᵢ − z̲ᵢ))`, `1 − δ̂ᵢ(z̄ᵢ − z̲ᵢ)/(2(z̄ᵢ − µᵢ)(µᵢ − z̲ᵢ))`, `δ̂ᵢ/(2(z̄ᵢ − µᵢ))` on `z̲ᵢ`, `µᵢ`,
`z̄ᵢ` and nothing elsewhere; if `zl i = zu i`, `P*(z̃ᵢ = µᵢ) = 1`.

**Formalization Note** "Independent of x" is carried by the formulas, which do not involve `x`.
The hypothesis `g(x, ·) > −∞` follows from the paper's standing assumption that Problem (2) has a
finite optimal value; this single-scenario statement assumes only the consequence it needs.
Masses are compared as real numbers (`P*` is a probability measure). -/
theorem proposition_1 {l m r n : ℕ} (W : Matrix (Fin r) (Fin l) ℝ) (U : Matrix (Fin r) (Fin m) ℝ)
    (V : Matrix (Fin r) (Fin n) ℝ) (v0 : Fin r → ℝ) (b : Fin m → ℝ) (μ δ zl zu : Fin n → ℝ)
    (hsc : ScenarioAssumptions μ δ zl zu) (x : Fin l → ℝ)
    (hbot : ∀ z, secondStageCost W U V v0 b x z ≠ ⊥) :
    ∃ P ∈ scenarioSet μ δ zl zu,
      DupacovaWets.Consistency.expect P (secondStageCost W U V v0 b x) =
        scenarioWorstCase (secondStageCost W U V v0 b x) μ δ zl zu ∧
      ∀ i, (zl i < zu i →
          (P {z | z i = zl i}).toReal = deltaHat (μ i) (δ i) (zl i) (zu i) / (2 * (μ i - zl i)) ∧
          (P {z | z i = μ i}).toReal = 1 - deltaHat (μ i) (δ i) (zl i) (zu i) * (zu i - zl i) /
            (2 * (zu i - μ i) * (μ i - zl i)) ∧
          (P {z | z i = zu i}).toReal = deltaHat (μ i) (δ i) (zl i) (zu i) / (2 * (zu i - μ i)) ∧
          P {z | z i ≠ zl i ∧ z i ≠ μ i ∧ z i ≠ zu i} = 0) ∧
        (zl i = zu i → P {z | z i = μ i} = 1) := by sorry

end SupermodDRO
