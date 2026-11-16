-- Prove2me | Theorems.Thm_SubmodSparsify_Supplement_theorem_A_1
-- name    : SubmodSparsify.Supplement.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:11:59.053663+00:00
-- url     : https://prove2.me/theorems/3c756b17-99c1-4b27-8c22-50d88e0e0d3f
-- title:
--   Theorem A.1 — Gibbs scores at integer $\beta$: $\sum_i p_i \le 2n(n-1)$, polynomial-time overestimates, and $\varepsilon$-sparsifiers of size $O(n^2\varepsilon^{-2}\log(2n/\delta))$
-- statement:
--   Let $F = \sum_{i=1}^m f_i$, where $f_1,\dots,f_m : 2^{[n]} \to \mathbb R_{\ge 0}$ are nonnegative submodular functions with $f_i(\emptyset) = f_i([n]) = 0$. Let $\beta \ge 1$ be an integer and let $p_1,\dots,p_m$ be the Gibbs scores of Algorithm 6 at inverse temperature $\beta$. There is a constant $C'$, not depending on $\beta$, such that:
--
--   1. $\displaystyle\sum_{i=1}^m p_i \le 2n(n-1).$
--   2. For fixed $\beta$ there is a randomized polynomial-time algorithm which, given $\delta \in (0,1)$, outputs on every run positive scores $\tilde p_1,\dots,\tilde p_m$ with $\sum_i \tilde p_i \le 4n(n-1)+1$, and with probability at least $1-\delta/4$ (over its coins) $\tilde p_i \ge p_i$ for every $i$.
--   3. For all $\varepsilon, \delta \in (0,1)$, run Algorithm 6 with $q = p$, or with $q = \tilde p$: discard identically zero components, set $\Lambda = 128\varepsilon^{-2}\log(64n/\delta)$, draw independent $\xi_i \sim \mathrm{Bernoulli}(\min\{1, \Lambda q_i\})$ and put $w_i = \xi_i/\min\{1,\Lambda q_i\}$. Then with probability at least $1-\delta$ (for $q = \tilde p$, jointly over the algorithm's coins and the draws), $\tilde F = \sum_i w_i f_i$ satisfies
--   $$|\tilde F(S) - F(S)| \le \varepsilon F(S) \quad \text{for every } S \subseteq [n]$$
--   and $|\operatorname{supp}(w)| \le C' n^2 \varepsilon^{-2}\log(2n/\delta)$.
--
--   The theorem shows that the "cooled" Gibbs distributions of the overview give importance weights as good as the ground-state weights of Theorem 4.1, and that they can be estimated efficiently by sampling from convex bodies.
--
--   **Formalization Note** "Polynomial time" refers to the randomized $m$-oracle RAM (`SubmodSparsify.Supplement.RMachine`): for each $\beta$ there are one admissible program and constants $C, k$ such that, on input $[n, m]$ and real $\delta$, on every coin tape the run halts within $\lceil C (n + m + \log(1/\delta) + 2)^k\rceil$ steps, with unit-cost value queries, and leaves $\tilde p_i$ in real-memory cell $i$. Probabilities over the tape use the fair-coin law `FasterSFM.coinTape` and are written as lower Lebesgue integrals, so no measurability is presupposed. Logarithms are natural.
--
--   Differences from the source:
--   - reading: "one can compute in polynomial time" → one admissible program of the randomized m-oracle RAM per β, halting on every coin tape within ⌈C(n + m + log(1/δ) + 2)^k⌉ steps with unit-cost queries, C and k depending on β only; reason: Lemma A.3 states time polynomial in n, m and log(1/δ′) for fixed β, with the unit-cost oracle of §A.4; a worst case over tapes is the standard meaning and is the stronger reading
--   - reading: "positive scores p̃ with Σ p̃ ≤ 4n(n−1)+1 such that, with probability at least 1−δ/4, p̃ᵢ ≥ pᵢ" → positivity and the sum bound on every coin tape, only p̃ ≥ p with probability ≥ 1 − δ/4; reason: the "such that" clause attaches the probability to p̃ ≥ p only, and the proof (p.45) gives the other two deterministically
--   - reading: "with probability at least 1 − δ" when run with p̃ → jointly over the coin tape and the Bernoulli draws (tape-average of the conditional sampling probability); reason: p̃ is random, and the proof (p.45) bounds the joint failure probability
--   - encoding: probabilities over the coin tape → lower Lebesgue integrals ∫⁻ against FasterSFM.coinTape; reason: no measurability presupposed; equals the probability for measurable events
--   - encoding: sparsity O(n²ε⁻² log(2n/δ)), "the constant does not depend on β" → ∃ C′ chosen before β, the program and the instance, on the same event as the approximation; reason: Lean rendering of O(·)
--   - encoding: "Discard identically zero components" → discardZero sets wᵢ = 0 when fᵢ(S) = 0 for every S; reason: Algorithm 6, line 2
--   - reading: Algorithm 6 discards identically zero components before scoring, and the theorem's "positive scores p̃₁, …, p̃_m" → the program receives all m components and outputs p̃ᵢ > 0 for every i, identically zero components included, with the sum over all m at most 4n(n−1)+1; zero components get weight 0 through discardZero; reason: the proof's p̃ᵢ = 1/m + Σ_u(s̃ᵢ⁽ᵘ⁾ + t̃ᵢ⁽ᵘ⁾) (p.45) does not need the discard (a zero component has zero shares), so this reading is at least the printed claim
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6793d37e5008919a4795e2e18da7fa5049f06ad4d1b929ac6d7fbc634), Theorem A.1, p.43 (PDF p.45); Algorithm 6, p.43; Lemma A.3, p.44; (67)–(68), p.47; proof pp.45–46

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_FasterSFM_Machine
import Definitions.Def_SubmodSparsify_bernProb
import Definitions.Def_SubmodSparsify_Supplement_gibbsScore
import Definitions.Def_SubmodSparsify_Supplement_RMachine

namespace SubmodSparsify.Supplement

open MeasureTheory

/-- **Theorem A.1** (p.43): sparsification with Gibbs scores at integer inverse temperature.

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Theorem A.1, p.43; Algorithm 6, p.43;
Lemma A.3, p.44; Appendix A preamble, p.42.

Let `F = Σᵢ fᵢ` with `f₁, …, f_m : {0,1}ⁿ → R≥0` nonnegative submodular, `fᵢ(∅) = fᵢ([n]) = 0`,
let `β ≥ 1` be an integer and `ε, δ ∈ (0, 1)`.
(a) The scores `pᵢ` of Algorithm 6 satisfy `Σᵢ pᵢ ≤ 2n(n − 1)`.
(b) For fixed `β`, a randomized algorithm computes in polynomial time positive scores `p̃ᵢ` with
`Σᵢ p̃ᵢ ≤ 4n(n − 1) + 1` such that, with probability at least `1 − δ/4`, `p̃ᵢ ≥ pᵢ` for every `i`.
(c) Running Algorithm 6 (`Λ = 128ε⁻² log(64n/δ)`, independent `ξᵢ ∼ Bernoulli(min{1, Λqᵢ})`,
`wᵢ = ξᵢ/min{1, Λqᵢ}`, identically zero components discarded) with `q = p`, or with `q = p̃`,
with probability at least `1 − δ` the sum `F̃ = Σᵢ wᵢfᵢ` satisfies `|F̃(S) − F(S)| ≤ εF(S)` for
every `S ⊆ [n]` and `|supp(w)| ≤ C′ n² ε⁻² log(2n/δ)`, where `C′` does not depend on `β`.

**Formalization Note.** `[n]` is `Fin n`, components `f : Fin m → Finset (Fin n) → ℝ` (paper
indices = values + 1). `gibbsScore β f` are the scores of Algorithm 6 (Gibbs shares (68) of the
`2n` terminal families); `discardZero f` sets the weight of an identically zero component to
`0` (line 2); `Λ = gibbsScale n ε δ`. The sample, `bernProb`, `sampledWeight`, `supportCard` are
those of the base module `SubmodSparsify.bernProb`. "Polynomial time" is a statement about the
randomized `m`-oracle RAM of module `SubmodSparsify.Supplement.RMachine` (the base machine with
the fair coin of `FasterSFM.Machine`) with input `[n, m]` in integer memory and `δ` in
real-memory cell `−1`, unit-cost value queries, and output `p̃ᵢ` in real-memory cell `i`: for
each `β` one admissible program `P` and constants `C, k` such that on every coin tape the run has
halted within `⌈C (n + m + log(1/δ) + 2)^k⌉` steps (worst case over tapes). Positivity and
`Σ p̃ ≤ 4n(n−1)+1` hold on every tape; the probabilities are over the fair-coin tape law
`FasterSFM.coinTape`, and in (c) with `q = p̃` jointly over the tape and the Bernoulli draws
(the tape-average of the conditional sampling probability). Both are lower Lebesgue integrals,
so no measurability is presupposed. `C′` is chosen before `β`, the program and the instance.
Logarithms are natural. -/
theorem theorem_A_1 :
    ∃ C' : ℝ, ∀ β : ℕ, 1 ≤ β →
      (∀ (n m : ℕ) (f : Fin m → Finset (Fin n) → ℝ) (hf0 : ∀ i S, 0 ≤ f i S)
          (hsub : ∀ i, NonmonotoneSubmod.Shared.Submodular (f i))
          (hempty : ∀ i, f i ∅ = 0) (huniv : ∀ i, f i Finset.univ = 0),
        ∑ i, gibbsScore β f i ≤ 2 * (n : ℝ) * ((n : ℝ) - 1)) ∧
      (∀ (n m : ℕ) (f : Fin m → Finset (Fin n) → ℝ) (hf0 : ∀ i S, 0 ≤ f i S)
          (hsub : ∀ i, NonmonotoneSubmod.Shared.Submodular (f i))
          (hempty : ∀ i, f i ∅ = 0) (huniv : ∀ i, f i Finset.univ = 0),
        ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
          1 - δ ≤ bernProb (sampleProb (gibbsScore β f) (gibbsScale n ε δ)) (fun ξ =>
            (∀ S : Finset (Fin n),
              |∑ i, discardZero f (sampledWeight (gibbsScore β f) (gibbsScale n ε δ) ξ) i *
                  f i S - ∑ i, f i S| ≤ ε * ∑ i, f i S) ∧
            (supportCard (discardZero f (sampledWeight (gibbsScore β f) (gibbsScale n ε δ) ξ)) :
                ℝ) ≤ C' * (n : ℝ) ^ 2 * ε⁻¹ ^ 2 * Real.log (2 * n / δ))) ∧
      (∃ (P : RProgram) (C : ℝ) (k : ℕ), RAdmissible P ∧
        ∀ (n m : ℕ) (f : Fin m → Finset (Fin n) → ℝ) (hf0 : ∀ i S, 0 ≤ f i S)
            (hsub : ∀ i, NonmonotoneSubmod.Shared.Submodular (f i))
            (hempty : ∀ i, f i ∅ = 0) (huniv : ∀ i, f i Finset.univ = 0)
            (δ : ℝ), 0 < δ → δ < 1 →
          let N : ℕ := ⌈C * ((n : ℝ) + (m : ℝ) + Real.log δ⁻¹ + 2) ^ k⌉₊
          let pt : (ℕ → Bool) → Fin m → ℝ := fun ω i =>
            (rrun P f [(n : ℤ), (m : ℤ)] δ ω N).base.core.mem ((i : ℕ) : ℤ)
          (∀ ω : ℕ → Bool, (rrun P f [(n : ℤ), (m : ℤ)] δ ω N).base.halted = true ∧
            (∀ i, 0 < pt ω i) ∧ ∑ i, pt ω i ≤ 4 * (n : ℝ) * ((n : ℝ) - 1) + 1) ∧
          ENNReal.ofReal (1 - δ / 4) ≤
            ∫⁻ ω, Set.indicator {ω | ∀ i, gibbsScore β f i ≤ pt ω i} 1 ω
              ∂FasterSFM.coinTape ∧
          ∀ ε : ℝ, 0 < ε → ε < 1 →
            ENNReal.ofReal (1 - δ) ≤
              ∫⁻ ω, ENNReal.ofReal (bernProb (sampleProb (pt ω) (gibbsScale n ε δ)) (fun ξ =>
                (∀ S : Finset (Fin n),
                  |∑ i, discardZero f (sampledWeight (pt ω) (gibbsScale n ε δ) ξ) i * f i S -
                      ∑ i, f i S| ≤ ε * ∑ i, f i S) ∧
                (supportCard (discardZero f (sampledWeight (pt ω) (gibbsScale n ε δ) ξ)) :
                    ℝ) ≤ C' * (n : ℝ) ^ 2 * ε⁻¹ ^ 2 * Real.log (2 * n / δ)))
                ∂FasterSFM.coinTape) := by sorry

end SubmodSparsify.Supplement
