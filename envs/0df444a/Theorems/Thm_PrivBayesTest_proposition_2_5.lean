-- Prove2me | Theorems.Thm_PrivBayesTest_proposition_2_5
-- name    : PrivBayesTest.proposition_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:25:10.82156+00:00
-- url     : https://prove2.me/theorems/f9cc0a9c-1e7e-4fa6-a325-404dcbfc291c
-- title:
--   Proposition 2.5: the dual optimizer is a shifted, scaled, clipped log-likelihood ratio, and the balancing condition
-- statement:
--   Let $P,Q$ be probability measures on $\mathcal X$ with densities $p,q$ with respect to $P+Q$, let $\alpha\in(0,1)$ and
--
--   $$
--   G_\alpha(\varphi)=-\alpha\log\int e^{-\varphi/\alpha}dP-(1-\alpha)\log\int e^{\varphi/(1-\alpha)}dQ .
--   $$
--
--   1. $G_\alpha$ is concave: for measurable $\varphi,\psi$ and $t\in[0,1]$, $(1-t)G_\alpha(\varphi)+tG_\alpha(\psi)\le G_\alpha((1-t)\varphi+t\psi)$.
--   2. Fix $\varepsilon>0$ and let $c=\tilde\alpha\varepsilon/2$. Then $\sup_{\|\varphi\|_\infty\le c}G_\alpha(\varphi)$ is attained.
--   3. Let $\varphi^*$ attain this supremum and put $\beta=\alpha(1-\alpha)$. Then there is a constant $t^*$ such that, with $c_2=c/\beta-t^*$, $c_1=-c/\beta-t^*$ and $\bar\ell=\min\{c_2,\max\{c_1,\log(p/q)\}\}$,
--   $$
--   \varphi^*=\beta(\bar\ell+t^*)\quad (P+Q)\text{-almost everywhere},
--   $$
--   4. and, with the same $\bar\ell$ (balancing condition),
--   $$
--   \inf_{R,S\in\Delta(\mathcal X)^2}\alpha\mathrm{KL}(R\|P)+(1-\alpha)\mathrm{KL}(S\|Q)+\tilde\alpha\varepsilon\mathrm{TV}(R,S)=-\log\int e^{(\alpha-1)\bar\ell}dP=-\log\int e^{\alpha\bar\ell}dQ .
--   $$
--
--   The clipped ratio $\bar\ell$ is the statistic of the optimal private test (§2.3).
--
--   Differences from the source:
--   - generalization: G_α concave on bounded functions φ → the concavity inequality for all measurable φ, ψ, with extended-real values; reason: specializes to bounded φ, where G_α is finite
--   - encoding: ‖φ‖∞ ≤ c → measurable φ with |φ(x)| ≤ c for every x; reason: the objective depends on φ only (P+Q)-almost everywhere
--   - reading: φ* = β(ℓ̄ + t*) → (P+Q)-almost everywhere, for every maximizer φ*; reason: pointwise equality is false: changing φ* on a (P+Q)-null set keeps it a maximizer
--   - reading: ℓ̄ in item 4 → the ℓ̄ of item 3, with one t* serving items 3 and 4; reason: item 4 refers to the ℓ̄ defined in item 3; the proof chooses t* = log(B(φ*)/A(φ*)) for both
--   - encoding: log(p/q) → ENNReal.log(p/q) as an extended real, with p, q the densities with respect to P + Q; reason: the paper's ±∞ conventions where p or q vanishes
--   - encoding: real-valued exponents, divergences and suprema → extended reals (EReal/ENNReal) with −log 0 = +∞; reason: Lean convention; avoids junk values of real sup/inf; same instances
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Proposition 2.5, pp.10–11

import Mathlib
import Definitions.Def_PrivBayesTest_klTvValue
import Definitions.Def_PrivBayesTest_dualObj
import Definitions.Def_PrivBayesTest_clipLLR

open MeasureTheory

namespace PrivBayesTest

/-- **Proposition 2.5** of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), pp.10–11. Fix probability measures `P, Q` and `α ∈ (0,1)`, and let
`G_α(φ) = −α log ∫ e^{−φ/α} dP − (1 − α) log ∫ e^{φ/(1−α)} dQ`. Then
1. `G_α` is a concave function of `φ`;
2. for `ε > 0` and `c = α̃ε/2`, the problem `sup_{‖φ‖∞ ≤ c} G_α(φ)` has a solution;
3. if `φ*` attains the optimum, there is a constant `t*` with `φ* = β(ℓ̄ + t*)`, where `β = α(1 − α)`,
   `ℓ̄ = min{c₂, max{c₁, log(p/q)}}`, `c₂ = c/β − t*`, `c₁ = −c/β − t*`;
4. (balancing condition) `inf_{R,S} α KL(R ∥ P) + (1 − α) KL(S ∥ Q) + α̃ε TV(R, S)
   = −log ∫ e^{(α−1)ℓ̄} dP = −log ∫ e^{αℓ̄} dQ`.

**Formalization Note** `G_α` is `PrivBayesTest.dualObj` (values in `EReal`). Item 1 is the
concavity inequality on all measurable `φ : X → ℝ` (extended-real values allowed), which contains
concavity on the bounded functions. `‖φ‖∞ ≤ c` is `|φ(x)| ≤ c` for every `x`. `p, q` are the densities of
`P, Q` with respect to `P + Q` and `ℓ̄` is `PrivBayesTest.clipLLR`. Items 3 and 4 are stated for
**every** maximizer `φ*`, with one `t*` serving both items; the identity `φ* = β(ℓ̄ + t*)` holds
`(P+Q)`-almost everywhere (a maximizer can be changed on a null set). -/
theorem proposition_2_5 {X : Type*} [MeasurableSpace X] (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ φ ψ : X → ℝ, Measurable φ → Measurable ψ → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ((1 - t : ℝ) : EReal) * dualObj P Q α φ + ((t : ℝ) : EReal) * dualObj P Q α ψ ≤
          dualObj P Q α (fun x => (1 - t) * φ x + t * ψ x)) ∧
      ∀ ε : ℝ, 0 < ε →
        (∃ φ : X → ℝ, Measurable φ ∧ (∀ x, |φ x| ≤ alphaTilde α * ε / 2) ∧
          ∀ ψ : X → ℝ, Measurable ψ → (∀ x, |ψ x| ≤ alphaTilde α * ε / 2) →
            dualObj P Q α ψ ≤ dualObj P Q α φ) ∧
        ∀ φ : X → ℝ, Measurable φ → (∀ x, |φ x| ≤ alphaTilde α * ε / 2) →
          (∀ ψ : X → ℝ, Measurable ψ → (∀ x, |ψ x| ≤ alphaTilde α * ε / 2) →
            dualObj P Q α ψ ≤ dualObj P Q α φ) →
          ∃ t : ℝ,
            (∀ᵐ x ∂(P + Q), φ x = α * (1 - α) * (clipLLR P Q
                (-(alphaTilde α * ε / 2) / (α * (1 - α)) - t)
                (alphaTilde α * ε / 2 / (α * (1 - α)) - t) x + t)) ∧
            ((klTvInf ε P Q α : ENNReal) : EReal) =
              -ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp ((α - 1) * clipLLR P Q
                (-(alphaTilde α * ε / 2) / (α * (1 - α)) - t)
                (alphaTilde α * ε / 2 / (α * (1 - α)) - t) x)) ∂P) ∧
            ((klTvInf ε P Q α : ENNReal) : EReal) =
              -ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (α * clipLLR P Q
                (-(alphaTilde α * ε / 2) / (α * (1 - α)) - t)
                (alphaTilde α * ε / 2 / (α * (1 - α)) - t) x)) ∂Q) := by sorry

end PrivBayesTest
