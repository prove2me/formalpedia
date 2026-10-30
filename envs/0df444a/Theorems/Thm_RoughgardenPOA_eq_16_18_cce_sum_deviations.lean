-- Prove2me | Theorems.Thm_RoughgardenPOA_eq_16_18_cce_sum_deviations
-- name    : RoughgardenPOA.eq_16_18_cce_sum_deviations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:37:13.244432+00:00
-- url     : https://prove2.me/theorems/57829d9a-4e44-479f-b455-6a69a69a790b
-- title:
--   (16)–(18): expected cost of a CCE is at most the expected deviation costs
-- statement:
--   Let $G$ be a cost-minimization game with players $1, \dots, k$, joint cost objective $C = \sum_i C_i$, let $\sigma$ be a coarse correlated equilibrium of $G$, and let $\mathbf s^*$ be any outcome. Then
--
--   $$\mathbf E_{\mathbf s\sim\sigma}[C(\mathbf s)] \le \sum_{i=1}^k \mathbf E_{\mathbf s\sim\sigma}[C_i(s_i^*, \mathbf s_{-i})].$$
--
--   This is the first half of the proof of the extension theorem: it is the only place where the equilibrium hypothesis is used, once per player with the hypothetical deviation $s_i^*$.
--
--   **Formalization Note** Players form a finite type, strategy spaces are arbitrary measurable spaces, $(s_i^*, \mathbf s_{-i})$ is `Function.update s i (sStar i)`, and every expectation is the Bochner integral of a function the coarse-correlated-equilibrium hypothesis makes integrable.
--
--   Differences from the source:
--   - encoding: players 1, …, k and the outcome (s*_i, s−i) → a finite type ι and Function.update s i (sStar i); reason: Lean convention; same instances
--   - encoding: a probability distribution σ over outcomes → a probability measure on the product σ-algebra of measurable strategy spaces; reason: Lean convention; a finite game is the case of discrete σ-algebras
--   - reading: the expectations in (15) and (16)–(18) → required to be finite (integrability conjuncts of IsCCE); reason: the paper writes these expectations as numbers; reading them in [0, ∞] makes the extension theorem false (two players, S_i = ℕ, C_i(s) = s_1 + s_2, i.i.d. heavy-tailed σ)
--   - reading: cost functions C_i → real-valued; reason: Definition 2.1 combines costs arithmetically (λ·C(s*) + µ·C(s)), so they are finite numbers
--   - generalization: nonnegative objective (p. 2) → costs of any sign; reason: the step does not use nonnegativity; the paper's games are the special case
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), doi:10.1145/2806883, §3.1, proof of Theorem 3.2, eqs. (16)–(18), p. 13

import Mathlib
import Definitions.Def_RoughgardenPOA_objective
import Definitions.Def_RoughgardenPOA_IsCCE

namespace RoughgardenPOA

/-- **(16)–(18): under a coarse correlated equilibrium, expected cost is at most the sum of
expected deviation costs.**
Roughgarden, *Intrinsic Robustness of the Price of Anarchy*, J. ACM 62(5) (2015),
doi:10.1145/2806883, §3.1, proof of Theorem 3.2, (16)–(18), p. 13:
"E_{s∼σ}[C(s)] = E_{s∼σ}[Σ_{i=1}^k Ci(s)] (16) = Σ_{i=1}^k E_{s∼σ}[Ci(s)] (17)
≤ Σ_{i=1}^k E_{s∼σ}[Ci(s*_i, s−i)] (18)".

For every cost-minimization game, every coarse correlated equilibrium `σ` and every outcome
`sStar`, `∫ s, objective C s ∂σ ≤ ∑ i, ∫ s, C i (Function.update s i (sStar i)) ∂σ`.

**Formalization Note.** `(s*_i, s−i)` is `Function.update s i (sStar i)`; every integral is of a
function that `IsCCE` makes integrable. `sStar` is an arbitrary outcome. -/
theorem eq_16_18_cce_sum_deviations
    {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (C : ι → (∀ i, S i) → ℝ) (σ : MeasureTheory.Measure (∀ i, S i)) (hσ : IsCCE C σ)
    (sStar : ∀ i, S i) :
    ∫ s, objective C s ∂σ ≤ ∑ i, ∫ s, C i (Function.update s i (sStar i)) ∂σ := by sorry

end RoughgardenPOA
