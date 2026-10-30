-- Prove2me | Theorems.Thm_RoughgardenPOA_theorem_3_2_fixed_pair
-- name    : RoughgardenPOA.theorem_3_2_fixed_pair
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:38:32.923217+00:00
-- url     : https://prove2.me/theorems/536fbeb8-6cea-4810-ad7c-c879b5a571fb
-- title:
--   Proof of Theorem 3.2: the bound $\lambda/(1-\mu)$ for one smooth pair
-- statement:
--   Let $G$ be a $(\lambda, \mu)$-smooth cost-minimization game with $\mu < 1$, let $\sigma$ be a coarse correlated equilibrium of $G$, and let $\mathbf s^*$ be any outcome of $G$. Then
--
--   $$\mathbf E_{\mathbf s\sim\sigma}[C(\mathbf s)] \le \frac{\lambda}{1-\mu} \cdot C(\mathbf s^*).$$
--
--   This is what the printed proof of Theorem 3.2 derives for a fixed smooth pair, by combining (16)–(18) with (19)–(21) and rearranging; the extension theorem itself then takes the infimum over all smooth pairs.
--
--   **Formalization Note** $\lambda$ is any real number and $\mathbf s^*$ is an arbitrary outcome, not necessarily optimal.
--
--   Differences from the source:
--   - encoding: players 1, …, k and the outcome (s*_i, s−i) → a finite type ι and Function.update s i (sStar i); reason: Lean convention; same instances
--   - encoding: a probability distribution σ over outcomes → a probability measure on the product σ-algebra of measurable strategy spaces; reason: Lean convention; a finite game is the case of discrete σ-algebras
--   - reading: the expectations in (15) and (16)–(18) → required to be finite (integrability conjuncts of IsCCE); reason: the paper writes these expectations as numbers; reading them in [0, ∞] makes the extension theorem false (two players, S_i = ℕ, C_i(s) = s_1 + s_2, i.i.d. heavy-tailed σ)
--   - reading: cost functions C_i → real-valued; reason: Definition 2.1 combines costs arithmetically (λ·C(s*) + µ·C(s)), so they are finite numbers
--   - generalization: nonnegative objective (p. 2) → costs of any sign; reason: the step does not use nonnegativity; the paper's games are the special case
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), doi:10.1145/2806883, §3.1, proof of Theorem 3.2, p. 13 ("Let G be a (λ, µ)-smooth cost-minimization game …", "Rearranging terms completes the proof")

import Mathlib
import Definitions.Def_RoughgardenPOA_objective
import Definitions.Def_RoughgardenPOA_IsSmooth
import Definitions.Def_RoughgardenPOA_IsCCE

namespace RoughgardenPOA

/-- **Proof of Theorem 3.2, p. 13: the bound `λ/(1 − µ)` for one smooth pair.**
Roughgarden, *Intrinsic Robustness of the Price of Anarchy*, J. ACM 62(5) (2015),
doi:10.1145/2806883, §3.1, proof of Theorem 3.2, p. 13: "Proof: Let G be a (λ, µ)-smooth
cost-minimization game, σ a coarse correlated equilibrium, and s* an outcome of G." …
"Rearranging terms completes the proof."

For a `(λ, µ)`-smooth cost-minimization game with `µ < 1`, every coarse correlated equilibrium
`σ` and every outcome `sStar`:
`∫ s, objective C s ∂σ ≤ lam / (1 - mu) * objective C sStar`.

**Formalization Note.** `lam` is any real number (Definition 2.1 imposes no sign); `mu < 1` is
Definition 2.2's constraint and makes `1 - mu > 0`. No nonnegativity of the objective is assumed.
`sStar` is an arbitrary outcome, not necessarily optimal. -/
theorem theorem_3_2_fixed_pair
    {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (C : ι → (∀ i, S i) → ℝ) (lam mu : ℝ) (hsm : IsSmooth C lam mu) (hmu : mu < 1)
    (σ : MeasureTheory.Measure (∀ i, S i)) (hσ : IsCCE C σ) (sStar : ∀ i, S i) :
    ∫ s, objective C s ∂σ ≤ lam / (1 - mu) * objective C sStar := by sorry

end RoughgardenPOA
