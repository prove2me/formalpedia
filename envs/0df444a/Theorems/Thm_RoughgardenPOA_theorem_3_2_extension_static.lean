-- Prove2me | Theorems.Thm_RoughgardenPOA_theorem_3_2_extension_static
-- name    : RoughgardenPOA.theorem_3_2_extension_static
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:39:26.085755+00:00
-- url     : https://prove2.me/theorems/0b9f1b00-df0c-4901-899c-adea71ad15d1
-- title:
--   Theorem 3.2 (Extension Theorem — Static Version): $\mathbf E_{\sigma}[C] \le \rho(G)\cdot C(\mathbf s^*)$
-- statement:
--   Let $G$ be a cost-minimization game with players $1, \dots, k$, strategy sets $S_i$, costs $C_i$ and joint cost objective $C = \sum_i C_i$, and let $\rho(G) \in [-\infty, +\infty]$ be its robust price of anarchy, the infimum of $\lambda/(1-\mu)$ over all real pairs $(\lambda, \mu)$ with $\mu < 1$ for which $G$ is $(\lambda,\mu)$-smooth. Then for every coarse correlated equilibrium $\sigma$ of $G$ and every outcome $\mathbf s^*$ of $G$,
--
--   $$\mathbf E_{\mathbf s\sim\sigma}[C(\mathbf s)] \le \rho(G) \cdot C(\mathbf s^*),$$
--
--   whenever the right-hand side is defined, i.e. unless $\rho(G) = +\infty$ and $C(\mathbf s^*) \le 0$.
--
--   Every price-of-anarchy bound proved by a smoothness argument for pure Nash equilibria therefore holds, with the same constant, for mixed Nash, correlated and coarse correlated equilibria; taking $\mathbf s^*$ optimal bounds the price of anarchy of all of these equilibrium concepts by $\rho(G)$.
--
--   **Formalization Note** The comparison is made in the extended reals. Mathlib's convention $(+\infty)\cdot 0 = 0$ would make the inequality false when $\rho(G) = +\infty$ and $C(\mathbf s^*) = 0$ (two-player coordination game with costs $0, 1$ on the diagonal and $2$ off it: no smooth pair with $\mu < 1$, a pure Nash equilibrium of cost $2$, an outcome of cost $0$); the hypothesis "$\rho(G) \ne +\infty$ or $C(\mathbf s^*) > 0$" excludes exactly that undefined case. The robust price of anarchy may also be $-\infty$, and costs may have any sign.
--
--   Differences from the source:
--   - encoding: ρ(G) = inf{λ/(1 − µ)} (possibly ±∞) and the product ρ(G)·C(s*) → the infimum and the product in EReal, under the hypothesis ρ(G) ≠ +∞ or C(s*) > 0; reason: with the paper's nonnegative objective the excluded case is ρ(G) = +∞, C(s*) = 0, where the paper's right-hand side ∞·0 is undefined; Mathlib's ⊤ * 0 = 0 would make the inequality false there (two-player coordination game counterexample)
--   - encoding: players 1, …, k and the outcome (s*_i, s−i) → a finite type ι and Function.update s i (sStar i); reason: Lean convention; same instances
--   - encoding: a probability distribution σ over outcomes → a probability measure on the product σ-algebra of measurable strategy spaces; reason: Lean convention; a finite game is the case of discrete σ-algebras
--   - reading: the expectations in (15) and in the conclusion → required to be finite (integrability conjuncts of IsCCE); reason: the paper writes these expectations as numbers; reading them in [0, ∞] makes the extension theorem false (two players, S_i = ℕ, C_i(s) = s_1 + s_2, i.i.d. heavy-tailed σ)
--   - reading: cost functions C_i → real-valued; reason: Definition 2.1 combines costs arithmetically (λ·C(s*) + µ·C(s)), so they are finite numbers
--   - generalization: nonnegative objective (p. 2) → costs of any sign; reason: the statement holds without nonnegativity (for C(s*) < 0 the bound for each smooth pair passes to the infimum); the paper's games are the special case
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), doi:10.1145/2806883, Theorem 3.2, p. 13

import Mathlib
import Definitions.Def_RoughgardenPOA_objective
import Definitions.Def_RoughgardenPOA_robustPOA
import Definitions.Def_RoughgardenPOA_IsCCE

namespace RoughgardenPOA

/-- **Theorem 3.2 (Extension Theorem — Static Version).**
Roughgarden, *Intrinsic Robustness of the Price of Anarchy*, J. ACM 62(5) (2015),
doi:10.1145/2806883, Theorem 3.2, p. 13: "For every cost-minimization game G with robust POA
ρ(G), every coarse correlated equilibrium σ of G, and every outcome s* of G,
E_{s∼σ}[C(s)] ≤ ρ(G) · C(s*)."

For every cost-minimization game (finitely many players `ι`, measurable strategy spaces `S i`,
real costs `C i`), every coarse correlated equilibrium `σ` and every outcome `sStar`, the
expected objective `∫ s, objective C s ∂σ`, as an extended real, is at most
`robustPOA C * objective C sStar`, provided `robustPOA C ≠ ⊤` or `objective C sStar > 0`.

**Formalization Note.** `ρ(G) = robustPOA C` is the `EReal` infimum of `λ/(1 − µ)` over every
real smooth pair with `µ < 1` (Definition 2.2). The hypothesis `hρ` excludes exactly the case
`ρ(G) = +∞` with `C(s*) ≤ 0`, where the paper's right-hand side is the undefined `∞ · 0` (the
paper's objective is nonnegative); Mathlib's convention `⊤ * 0 = 0` would make the inequality
false there (two-player coordination game: `ρ = +∞`, a pure Nash equilibrium of cost 2, and an
outcome of cost 0). When `ρ(G) = +∞` and `C(s*) > 0` the conclusion is the paper's `E ≤ +∞`.
No nonnegativity of the objective, no `λ > 0` and no optimality of `sStar` is assumed. -/
theorem theorem_3_2_extension_static
    {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (C : ι → (∀ i, S i) → ℝ) (σ : MeasureTheory.Measure (∀ i, S i)) (hσ : IsCCE C σ)
    (sStar : ∀ i, S i) (hρ : robustPOA C ≠ ⊤ ∨ 0 < objective C sStar) :
    ((∫ s, objective C s ∂σ : ℝ) : EReal) ≤ robustPOA C * ((objective C sStar : ℝ) : EReal) := by sorry

end RoughgardenPOA
