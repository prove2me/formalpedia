-- Prove2me | Theorems.Thm_RandOrderSort_lemma_4_16
-- name    : RandOrderSort.lemma_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:17.764095+00:00
-- url     : https://prove2.me/theorems/73c32eeb-99f3-4be6-9d55-78405ed93d9e
-- title:
--   Lemma 4.16 — transfer at a binomial mode
-- statement:
--   Suppose a deterministic comparison-based algorithm satisfies
--   $$\mathbb E[e^{\theta C(q)}]\le A_0n^{\gamma_0}$$
--   under i.i.d. uniform input, uniformly in deterministic $q\in(0,1)$. Then, for every fixed strict input exposed in a uniform random permutation,
--   $$\mathbb E_\pi[e^{\theta C_a}]\le 2A_0n^{\gamma_0+1}\qquad(1\le a<n).$$
--
--   Here $C_a$ counts adjacent output pairs with one rank at most $a$ and the other greater than $a$. Placement decisions depend only on the relative order of the inputs, which is what carries the bound from value cuts to rank cuts.
--
--   **Formalization Note** The algorithm is any `OnlineCmpAlg`, and a fixed strict input is an injective $x$, so the priorities play no role. The integrand of the hypothesis is automatically integrable, being a bounded function of finitely many measurable comparisons.
--
--   Differences from the source:
--   - generalization: a hypothesis uniform in n, with the constants of Proposition 4.15 → a hypothesis at one n giving the conclusion at that n, for arbitrary real θ, A₀, γ₀; reason: the page's hypothesis gives the Lean hypothesis at each n and Proposition 4.15's constants are special values
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Lemma 4.16, p.37

import Mathlib
import Definitions.Def_RandOrderSort_OnlineCmpAlg
import Definitions.Def_RandOrderSort_iidUnif
open MeasureTheory

namespace RandOrderSort

/-- **Lemma 4.16 (Transfer at a binomial mode)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.37: "Suppose a deterministic
comparison-based algorithm satisfies E[e^{θC(q)}] ≤ A_0 n^{γ_0} under i.i.d. uniform input, uniformly in
deterministic q ∈ (0, 1) and n. Then, for every fixed strict input exposed in a uniform random
permutation, E_π[e^{θC_a}] ≤ 2A_0 n^{γ_0+1} (1 ≤ a < n)."

**Formalization Note.** For every comparison-only online algorithm `A` and all real constants
`θ`, `A_0`, `γ_0`. The hypothesis is used at one `n` at a time: for each `n`, the bound for every
`q ∈ (0,1)` at that `n` gives the conclusion at that `n` (this contains the paper's statement, whose
hypothesis holds for all `n`). The integrand of the hypothesis is automatically integrable: it is a
bounded function of finitely many measurable comparisons of the inputs. A fixed strict input is an
injective `x`, so the priorities play no role (`σ = 1`); `C_a` is `rankCrossings` and `E_π` the
uniform expectation over `π`. -/
theorem lemma_4_16 : ∀ (A : OnlineCmpAlg) (θ A₀ γ₀ : ℝ) (n : ℕ),
    (∀ q : ℝ, 0 < q → q < 1 →
      ∫ X, Real.exp (θ * valueCrossings A X 1 1 q) ∂(iidUnif n) ≤ A₀ * (n : ℝ) ^ γ₀) →
    ∀ x : Fin n → ℝ, Function.Injective x → ∀ a : ℕ, 1 ≤ a → a < n →
      uniformExp (fun π : Equiv.Perm (Fin n) => Real.exp (θ * rankCrossings A x π 1 a)) ≤
        2 * A₀ * (n : ℝ) ^ (γ₀ + 1) := by sorry

end RandOrderSort
