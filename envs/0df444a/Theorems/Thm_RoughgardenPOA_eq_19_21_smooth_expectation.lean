-- Prove2me | Theorems.Thm_RoughgardenPOA_eq_19_21_smooth_expectation
-- name    : RoughgardenPOA.eq_19_21_smooth_expectation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:37:50.461613+00:00
-- url     : https://prove2.me/theorems/919ab4de-9e72-45bd-8667-e754039c4284
-- title:
--   (19)–(21): smoothness bounds the expected deviation costs
-- statement:
--   Let $G$ be a $(\lambda, \mu)$-smooth cost-minimization game with joint cost objective $C$, let $\mathbf s^*$ be any outcome, and let $\sigma$ be a probability distribution over outcomes under which every $C_i(\mathbf s)$ and every $C_i(s_i^*, \mathbf s_{-i})$ has a finite expectation. Then
--
--   $$\sum_{i=1}^k \mathbf E_{\mathbf s\sim\sigma}[C_i(s_i^*, \mathbf s_{-i})] \le \lambda \cdot C(\mathbf s^*) + \mu \cdot \mathbf E_{\mathbf s\sim\sigma}[C(\mathbf s)].$$
--
--   This is the second half of the proof of the extension theorem: it uses only smoothness and linearity of expectation, not the equilibrium property.
--
--   **Formalization Note** No sign condition on $\lambda$, $\mu$ and no $\mu < 1$ is needed for this step.
--
--   Differences from the source:
--   - generalization: σ a coarse correlated equilibrium → σ any probability measure under which the costs and the deviation costs are integrable; reason: the steps (19)–(21) use only linearity of expectation and smoothness; a coarse correlated equilibrium is such a measure
--   - encoding: players 1, …, k and the outcome (s*_i, s−i) → a finite type ι and Function.update s i (sStar i); reason: Lean convention; same instances
--   - encoding: a probability distribution σ over outcomes → a probability measure on the product σ-algebra of measurable strategy spaces; reason: Lean convention; a finite game is the case of discrete σ-algebras
--   - reading: the expectations in (19)–(21) → required to be finite (integrability hypotheses hC, hdev); reason: the paper writes these expectations as numbers; reading them in [0, ∞] makes the extension theorem false (two players, S_i = ℕ, C_i(s) = s_1 + s_2, i.i.d. heavy-tailed σ)
--   - reading: cost functions C_i → real-valued; reason: Definition 2.1 combines costs arithmetically (λ·C(s*) + µ·C(s)), so they are finite numbers
--   - generalization: nonnegative objective (p. 2) → costs of any sign; reason: the step does not use nonnegativity; the paper's games are the special case
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), doi:10.1145/2806883, §3.1, proof of Theorem 3.2, eqs. (19)–(21), p. 13

import Mathlib
import Definitions.Def_RoughgardenPOA_objective
import Definitions.Def_RoughgardenPOA_IsSmooth

namespace RoughgardenPOA

/-- **(19)–(21): smoothness bounds the expected sum of deviation costs.**
Roughgarden, *Intrinsic Robustness of the Price of Anarchy*, J. ACM 62(5) (2015),
doi:10.1145/2806883, §3.1, proof of Theorem 3.2, (19)–(21), p. 13:
"= E_{s∼σ}[Σ_{i=1}^k Ci(s*_i, s−i)] (19) ≤ E_{s∼σ}[λ · C(s*) + µ · C(s)] (20)
= λ · C(s*) + µ · E_{s∼σ}[C(s)], (21)".

For a `(λ, µ)`-smooth cost-minimization game, every probability measure `σ` on outcomes under
which each `C i` and each deviation cost `s ↦ C i (s*_i, s−i)` is integrable, and every outcome
`sStar`:
`∑ i, ∫ s, C i (Function.update s i (sStar i)) ∂σ ≤ lam * objective C sStar + mu * ∫ s, objective C s ∂σ`.

**Formalization Note.** The paper applies these steps to a coarse correlated equilibrium; the
steps use only that `σ` is a probability distribution under which the expectations exist, so the
statement is made for every such `σ`. No sign condition on `lam` or `mu` and no `mu < 1` is
needed. -/
theorem eq_19_21_smooth_expectation
    {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (C : ι → (∀ i, S i) → ℝ) (lam mu : ℝ) (hsm : IsSmooth C lam mu)
    (σ : MeasureTheory.Measure (∀ i, S i)) [MeasureTheory.IsProbabilityMeasure σ]
    (sStar : ∀ i, S i)
    (hC : ∀ i, MeasureTheory.Integrable (C i) σ)
    (hdev : ∀ i, MeasureTheory.Integrable (fun s => C i (Function.update s i (sStar i))) σ) :
    ∑ i, ∫ s, C i (Function.update s i (sStar i)) ∂σ ≤
      lam * objective C sStar + mu * ∫ s, objective C s ∂σ := by sorry

end RoughgardenPOA
