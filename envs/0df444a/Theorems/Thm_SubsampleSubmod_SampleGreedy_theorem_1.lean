-- Prove2me | Theorems.Thm_SubsampleSubmod_SampleGreedy_theorem_1
-- name    : SubsampleSubmod.SampleGreedy.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:08.400713+00:00
-- url     : https://prove2.me/theorems/13111b08-72cc-4f5d-9bbd-02a707272684
-- title:
--   Theorem 1, p. 7 — SampleGreedy is a (p+1)²/p-approximation (p+1 monotone, q = 1/(p+1); p linear, q = 1/p) over p-extendible systems
-- statement:
--   Let $\mathcal N$ be a finite ground set with a fixed linear order (used to break ties), let $f : 2^{\mathcal N} \to \mathbb R_{\ge 0}$ be a non-negative submodular function, and let $(\mathcal N, \mathcal I)$ be a $p$-extendible independence system with $p \ge 1$. Write $\mathbb E_q[f(S)]$ for the expected value of the set $S$ returned by SampleGreedy (Algorithm 1) when every element is sampled independently with probability $q$. Then:
--
--   1. SampleGreedy always returns an independent set: $S \in \mathcal I$ for every sample.
--   2. With $q = \frac{1}{p+1}$, for every independent set $T \in \mathcal I$,
--   $$f(T) \;\le\; \frac{(p+1)^2}{p}\; \mathbb E_{1/(p+1)}[f(S)].$$
--   3. If moreover $f$ is monotone, then with $q = \frac{1}{p+1}$, $f(T) \le (p+1)\, \mathbb E_{1/(p+1)}[f(S)]$ for every $T \in \mathcal I$.
--   4. If moreover $f$ is linear, then with $q = \frac1p$, $f(T) \le p\, \mathbb E_{1/p}[f(S)]$ for every $T \in \mathcal I$.
--
--   Taking $T$ to be a maximizer OPT of problem (2), these say that SampleGreedy is, in expectation, a $(p+1)^2/p$-approximation for non-negative submodular maximization over $p$-extendible systems, a $(p+1)$-approximation for monotone objectives, and a $p$-approximation for linear objectives. Since no polynomial-query algorithm beats $p + 1/2$ for this problem, the ratio $(p+1)^2/p = p + 2 + 1/p$ is nearly tight.
--
--   **Formalization Note** The approximation ratio of a randomized algorithm is read as the paper's proof reads it: $\mathbb E[f(S)] \ge f(\mathrm{OPT})/\alpha$. Comparing with every $T \in \mathcal I$ is equivalent to comparing with OPT. Additions relative to the page: $p$ is a natural number with $p \ge 1$ (the paper divides by $p$); ties are broken by a fixed linear order of the ground set, as the paper assumes on p. 10; the expectation is the exact sum over all $2^n$ samples; the while loop runs $n$ iterations. "Linear" is the page's definition ((1) with equality) and does not force $f(\emptyset) = 0$. Submodularity is the published lattice form, equivalent on finite ground sets to the diminishing-returns form (1). The oracle-count clause "SampleGreedy uses in expectation $O(nk/p)$ calls to the evaluation and independence oracles" is not formalized.
-- source:
--   Harshaw et al., arXiv:2104.02772v1, p. 7, Theorem 1 (proof §4.1, pp. 9–17: §4.1.1 pp. 14–15 submodular, §4.1.2 p. 17 linear)

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Model

namespace SubsampleSubmod.SampleGreedy

/-- Theorem 1 (Harshaw et al., arXiv:2104.02772v1, p. 7). Let `f ≥ 0` be submodular and `ℐ` a
`p`-extendible independence system, `p ≥ 1`. SampleGreedy always returns an independent set, and
1. with `q = 1/(p+1)`: `f(T) ≤ (p+1)²/p · E[f(S)]` for every `T ∈ ℐ`;
2. with `q = 1/(p+1)` and `f` monotone: `f(T) ≤ (p+1) · E[f(S)]` for every `T ∈ ℐ`;
3. with `q = 1/p` and `f` linear: `f(T) ≤ p · E[f(S)]` for every `T ∈ ℐ`.
The oracle-count clause `O(nk/p)` is not formalized. -/
theorem theorem_1 {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hp : 1 ≤ p) (hf0 : ∀ S, 0 ≤ f S)
    (hsub : NonmonotoneSubmod.Shared.Submodular f) (hI : IsIndepSystem I)
    (hext : IsPExtendible p I) :
    (∀ N' : Finset α, I (sampleGreedy f I N')) ∧
    (∀ T : Finset α, I T →
      f T ≤ (((p : ℝ) + 1) ^ 2 / (p : ℝ)) * expectedValue (1 / ((p : ℝ) + 1)) f I) ∧
    (Monotone f → ∀ T : Finset α, I T →
      f T ≤ ((p : ℝ) + 1) * expectedValue (1 / ((p : ℝ) + 1)) f I) ∧
    (IsLinear f → ∀ T : Finset α, I T →
      f T ≤ (p : ℝ) * expectedValue (1 / (p : ℝ)) f I) := by sorry

end SubsampleSubmod.SampleGreedy
