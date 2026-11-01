-- Prove2me | Theorems.Thm_SambaPG_lemma_7
-- name    : SambaPG.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:37:50.479191+00:00
-- url     : https://prove2.me/theorems/f77bbc1d-360b-4f8a-92e0-106ec055579d
-- title:
--   Lemma 7 — geometric trials give a finite expected hitting time of $C$ (corrected: return time to $B\cup C$; chain stays in $A\cup B\cup C$ from $B$)
-- statement:
--   Let $(X(t):t\in\mathbb Z_+)$ be a time-homogeneous Markov chain with transition kernel $P$ on a measurable space $\mathcal X$, and write $\mathbb P_x$, $\mathbb E_x$ for the law of its path started at $x$. Let $A,B,C$ be disjoint measurable subsets of $\mathcal X$, $n\in\mathbb Z_+$, $\delta>0$ and $K<\infty$ such that
--
--   1. (25a) for every $x_0\in B$: $\ \mathbb P_{x_0}\big(X(n)\in C,\ X(k)\notin A\ \forall k<n\big)\ge\delta$;
--   2. (25b, corrected) for every $x_0\in B$ and $P(x_0,\cdot)$-almost every $x_1\in A$:
--   $$
--   \mathbb E[\tau^+\mid X(1)=x_1,X(0)=x_0]=1+\mathbb E_{x_1}\big[\min\{t\ge0:X(t)\in B\cup C\}\big]<K,
--   $$
--   where $\tau^+=\min\{t\ge1:X(t)\in B\cup C\}$ is the return time to $B\cup C$;
--   3. (corrected) from every $x_0\in B$ the chain moves into $A\cup B\cup C$: $P(x_0,(A\cup B\cup C)^c)=0$.
--
--   Then $\tau_C:=\min\{t\in\mathbb Z_+:X(t)\in C\}$ satisfies
--
--   $$
--   \sup_{x_0\in B}\mathbb E_{x_0}[\tau_C]<\infty .
--   $$
--
--   From $B$ the chain has, at each visit, a chance at least $\delta$ of reaching $C$ within $n$ steps, and excursions into $A$ return in bounded expected time, so $C$ is reached after a geometric number of trials.
--
--   **Formalization Note** The path law $\mathbb P_x$ is the platform's `MarkovChainKernel`. Hitting times take values in $\mathbb N\cup\{\infty\}$ and expectations are integrals in $[0,\infty]$.
--
--   Differences from the source:
--
--   - correction: (25b) with τ_B = min{t ∈ ℤ₊ : X(t) ∈ B} → (25b) with the return time τ⁺ = min{t ≥ 1 : X(t) ∈ B ∪ C}; reason: given X(0) = x₀ ∈ B the printed τ_B is 0, so (25b) always holds, and the lemma is false: B = {0}, C = {−1} absorbing, A = {1, 2, …}; from 0 go to −1 w.p. 1/2, else to k w.p. (3/π²)k⁻², then walk down to 0; (25a) holds with n = 1, δ = 1/2, but E₀τ_C ≥ Σ(3/π²)k⁻²·k = ∞. The proof (p.25) and the application (p.23) use the return time
--   - correction: no condition on where the chain goes from B → P(x₀, (A ∪ B ∪ C)ᶜ) = 0 for x₀ ∈ B; reason: otherwise the same heavy-tailed excursion placed in a fourth region D satisfies (25a) and (25b) and gives E₀τ_C = ∞; in the application A, B, C partition the simplex
--   - reading: E[τ | X(1) = x₁, X(0) = x₀] and sup over x₁ ∈ A → for P(x₀, ·)-almost every x₁ ∈ A, 1 + E_{x₁}[hitting time of B ∪ C]; reason: conditioning on a point is defined only almost everywhere; a supremum over unreachable x₁ would fail in the application
--   - generalization: a Markov chain on 𝒳 ⊂ ℝᵈ → a time-homogeneous chain given by a Markov kernel on any measurable space; reason: contains every subset of ℝᵈ with its Borel σ-algebra
--   - encoding: subsets A, B, C; δ > 0; K < ∞; sup … < ∞ → measurable A, B, C; δ, K in [0, ∞]; one finite bound M for all x₀ ∈ B; ℕ∞ hitting times with lintegral expectations; reason: probabilities of the sets must be defined; infinite times count as ∞
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, Lemma 7, p.23 (proof §A.4, p.25; application p.23)

import Mathlib
import Definitions.Def_MarkovChainKernel
import Definitions.Def_SambaPG_firstHitFrom

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SambaPG

/-- **Lemma 7 (geometric trials; corrected).**
Denisov & Walton, arXiv:2007.10229v3, Lemma 7, p.23 (proof §A.4, p.25).

Let `X` be a time-homogeneous Markov chain with transition kernel `P` on a measurable space `𝒳`, and
write `ℙ_x` for the law of its path started at `x` (`BanditAlgorithm.markovChainKernel P x`). Let
`A, B, C` be disjoint measurable subsets of `𝒳`, `n ∈ ℕ`, `δ > 0` and `K < ∞` such that
* (25a) for all `x₀ ∈ B`: `ℙ_{x₀}(X(n) ∈ C, X(k) ∉ A ∀ k < n) ≥ δ`;
* (25b, corrected) for all `x₀ ∈ B` and `P(x₀, ·)`-almost every `x₁ ∈ A`:
  `E[τ⁺ | X(1) = x₁, X(0) = x₀] = 1 + E_{x₁}[min{t ≥ 0 : X(t) ∈ B ∪ C}] < K`,
  where `τ⁺ = min{t ≥ 1 : X(t) ∈ B ∪ C}` is the return time to `B ∪ C`;
* (support, corrected) from every `x₀ ∈ B` the chain moves into `A ∪ B ∪ C`.

Then `τ_C := min{t ∈ ℤ₊ : X(t) ∈ C}` satisfies `sup_{x₀ ∈ B} E[τ_C | X(0) = x₀] < ∞`.

**Formalization Note.** As printed, (25b) uses `τ_B = min{t ∈ ℤ₊ : X(t) ∈ B}`, which is `0` given
`X(0) = x₀ ∈ B`, and the lemma is then false; and a chain that leaves `B` for a fourth region also
falsifies it. Both counterexamples are in the mission notes. The corrected (25b) uses the return
time to `B ∪ C`, which is the time the proof (p.25) and the application (p.23) use. Conditioning on
the points `X(1) = x₁`, `X(0) = x₀` is expressed through the kernel: for `P(x₀, ·)`-a.e. `x₁`. The
state space is any measurable space (the paper: `𝒳 ⊂ ℝᵈ`). Hitting times are `ℕ∞`-valued and the
expectations are `lintegral`s. -/
theorem lemma_7 {X : Type*} [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P]
    {A B C : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (n : ℕ) {δ : ℝ≥0∞} (hδ : 0 < δ) {K : ℝ≥0∞} (hK : K < ⊤)
    (h25a : ∀ x₀ ∈ B,
      δ ≤ BanditAlgorithm.markovChainKernel P x₀ {ω | ω n ∈ C ∧ ∀ k < n, ω k ∉ A})
    (h25b : ∀ x₀ ∈ B, ∀ᵐ x₁ ∂(P x₀), x₁ ∈ A →
      1 + ∫⁻ ω, ((firstHitFrom (fun t => ω t ∈ B ∪ C) 0 : ℕ∞) : ℝ≥0∞)
        ∂(BanditAlgorithm.markovChainKernel P x₁) < K)
    (hsupp : ∀ x₀ ∈ B, P x₀ (A ∪ B ∪ C)ᶜ = 0) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ x₀ ∈ B,
      ∫⁻ ω, ((firstHitFrom (fun t => ω t ∈ C) 0 : ℕ∞) : ℝ≥0∞)
        ∂(BanditAlgorithm.markovChainKernel P x₀) ≤ M := by sorry

end SambaPG
