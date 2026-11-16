-- Prove2me | Theorems.Thm_SubmodSparsify_Supplement_theorem_5_1
-- name    : SubmodSparsify.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:11:15.628198+00:00
-- url     : https://prove2.me/theorems/2327211d-b6ef-451b-b7ba-23cf2b3c21c8
-- title:
--   Theorem 5.1 — cardinality-bounded sparsifiers of size $O(nk\varepsilon^{-2}\log(2n/\delta))$ with $\sum_i p_i \le 10nk$
-- statement:
--   Let $F = \sum_{i=1}^m f_i$, where $f_1,\dots,f_m : 2^{[n]} \to \mathbb R_{\ge 0}$ are nonnegative submodular functions with $f_i(\emptyset) = f_i([n]) = 0$, and let $1 \le k \le n$. Let $p_1,\dots,p_m$ be the scores (37) of Algorithm 3, computed from a low-collision partition family produced by Algorithm 5 (distinct labels $x_v \in \mathbb F_M$ and a surjective $\mathbb F_2$-linear map $\varphi$).
--
--   1. For every such choice, $\displaystyle\sum_{i=1}^m p_i \le 10nk.$
--   2. There is an absolute constant $C$ such that for every time bound $T$ for submodular function minimization ($T_{\min}(n) \le T(n)$), one program on the deterministic $m$-oracle RAM computes the scores of some admissible choice, on every instance with $m \ge 1$, in time
--   $$C\, m\, n^3 k\, T(n)^2\, (T_{\mathrm{eval}} + n)$$
--   when each value query costs $T_{\mathrm{eval}} \ge 1$.
--   3. There is an absolute constant $C'$ such that for every admissible choice and all $\varepsilon, \delta \in (0,1)$, with $\Lambda = 56\varepsilon^{-2}\log(32n/\delta)$, sampling each $f_i$ independently with probability $\min\{1, \Lambda p_i\}$ and weight $w_i = 1/\min\{1,\Lambda p_i\}$ (and $w_i = 0$ otherwise), with probability at least $1-\delta$ the sum $\tilde F = \sum_i w_i f_i$ satisfies
--   $$|\tilde F(S) - F(S)| \le \varepsilon F(S) \quad \text{for every } S \subseteq [n] \text{ with } |S| \le k,$$
--   and $|\operatorname{supp}(w)| \le C' n k \varepsilon^{-2} \log(2n/\delta)$.
--
--   This is the cardinality-constrained counterpart of Theorem 4.1: restricting queries to sets of size at most $k$ reduces the sparsifier size from $O(\varepsilon^{-2} n^2 \log(2n/\delta))$ to $O(\varepsilon^{-2} nk \log(2n/\delta))$, which Proposition 6.1 shows is tight up to the logarithm.
--
--   **Formalization Note** $[n]$ is `Fin n`; the time model, $T_{\min}$ and $T_{\mathrm{eval}}$ are exactly those of the base goal (Theorem 4.1): `SFMTime T`, the base `SubmodSparsify.Machine` with input $[n, m, k]$, output $p_i$ in real-memory cell $i$, and `charged`. Logarithms are natural.
--
--   Differences from the source:
--   - reading: time "in time (mn³k Tmin(n)²(Teval + n))" printed without O → ∃ absolute C (chosen before T and the program) with charged time ≤ C·m n³ k T(n)²(Teval + n); reason: the printed theorem drops the O by a typo; Claim 5.3's paragraph (p.31) and (59) (p.39) state O(mn³k Tmin(n)²(Teval + n)), and the proof gives no constant 1
--   - reading: "Algorithm 3 computes weights p₁,…,p_m" with Algorithm 5's labels and φ left free → Σpᵢ ≤ 10nk and the sampling guarantee for every injective labelling and surjective linear φ, the program outputs the scores of some such choice; reason: Algorithm 5 fixes the labels and φ arbitrarily and the proof (Claim 5.3) works for every choice
--   - encoding: size-O(nkε⁻² log(2n/δ)) → ∃ absolute C′ (chosen before n, m, k, f, the labels, φ, ε, δ) with |supp(w)| ≤ C′ nkε⁻² log(2n/δ), on the same event as the approximation; reason: Lean rendering of O(·)
--   - encoding: "in time" for all instances → for instances with m ≥ 1 (n ≥ k ≥ 1 already); reason: the bound concerns nonempty instances, as in the base goal
--   - encoding: Tmin(n), Teval → `SFMTime T` (Tmin ≤ T) and the per-query charge `charged s Teval` for every Teval ≥ 1; reason: the base goal's model of the paper's p.3 definitions
--   - encoding: "sparsifier of F under the cardinality constraint x ∈ ([n] choose ≤k)", i.e. F̃(S) = (1 ± ε)·F(S) for all S with |S| ≤ k (definition (2), p.2) → |F̃(S) − F(S)| ≤ ε·F(S) for every S : Finset (Fin n) with S.card ≤ k; reason: the same condition written as one inequality
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6793d37e5008919a4795e2e18da7fa5049f06ad4d1b929ac6d7fbc634), Theorem 5.1, p.28 (PDF p.30); Algorithm 3, p.28; Algorithm 5, p.31; (37), p.32; (59), p.39

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubmodSparsify_weights
import Definitions.Def_SubmodSparsify_bernProb
import Definitions.Def_SubmodSparsify_Machine
import Definitions.Def_SubmodSparsify_SFMTime
import Definitions.Def_SubmodSparsify_Supplement_cardScore

namespace SubmodSparsify.Supplement

/-- **Theorem 5.1** (p.28): sparsification for cardinality-bounded queries.

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Theorem 5.1, p.28; Algorithm 3, p.28;
(37), p.32; time bound (59), p.39.

Let `F = Σᵢ fᵢ` with `f₁, …, f_m : {0,1}ⁿ → R≥0` nonnegative submodular, `fᵢ(∅) = fᵢ([n]) = 0`,
and let `1 ≤ k ≤ n`.
(a) Algorithm 3's scores satisfy `Σᵢ pᵢ ≤ 10nk`, for every partition family Algorithm 5 can
produce.
(b) Algorithm 3 computes them deterministically in time `O(mn³k Tmin(n)²(Teval + n))`.
(c) For `ε, δ ∈ (0, 1)` and `Λ = 56ε⁻² log(32n/δ)`, sampling each `fᵢ` independently with
probability `min{1, Λpᵢ}` and weight `wᵢ = 1/min{1, Λpᵢ}` (else `0`), with probability at least
`1 − δ` the sum `F̃ = Σᵢ wᵢfᵢ` satisfies `|F̃(S) − F(S)| ≤ εF(S)` for every `S` with `|S| ≤ k`
and `|supp(w)| ≤ C′ nk ε⁻² log(2n/δ)`, for one absolute constant `C′`.

**Formalization Note.** `[n]` is `Fin n`, components `f : Fin m → Finset (Fin n) → ℝ` (paper
indices = values + 1). The scores are `cardScore f k x φ` (module
`SubmodSparsify.Supplement.cardScore`): (37) for the low-collision family of Algorithm 5 built
from distinct labels `x` (`x` injective) and a surjective `F₂`-linear `φ`. Algorithm 5 leaves
`(x, φ)` free, so (a) and (c) hold for every admissible choice, and in (b) the program outputs the
scores of some admissible choice. `SFMTime T` (base module) says `Tmin(n) ≤ T(n)`; Algorithm 3
runs on the deterministic `m`-oracle RAM `SubmodSparsify.Machine` of the base mission with input
`[n, m, k]` in integer memory and halts with `pᵢ` in real-memory cell `i`; `charged s Teval` is
the running time when each value query costs `Teval`. The printed bound is read as `O(·)` (§5.4,
(59)): one absolute constant `C`, chosen before `T` and the program; `m ≥ 1` in (b) (nonempty
instances; `n ≥ k ≥ 1` already). In (c) the sample, its law `bernProb`, the weights
`sampledWeight` and `|supp(w)| = supportCard` are those of the base module
`SubmodSparsify.bernProb`; `Λ = samplingScale n ε δ` (base); "sparsifier under the cardinality
constraint" (p.2) is `|F̃(S) − F(S)| ≤ εF(S)` for every `|S| ≤ k`; both properties hold on one
event; `C′` is chosen before `n, m, k, f, x, φ, ε, δ`. Logarithms are natural. -/
theorem theorem_5_1 :
    (∀ (n m : ℕ) (f : Fin m → Finset (Fin n) → ℝ) (hf0 : ∀ i S, 0 ≤ f i S)
        (hsub : ∀ i, NonmonotoneSubmod.Shared.Submodular (f i))
        (hempty : ∀ i, f i ∅ = 0) (huniv : ∀ i, f i Finset.univ = 0)
        (k : ℕ), 1 ≤ k → k ≤ n →
      ∀ (x : Fin n → LCField n k) (φ : LCField n k →ₗ[ZMod 2] BlockLabel k),
        Function.Injective x → Function.Surjective φ →
          ∑ i, cardScore f k x φ i ≤ 10 * (n : ℝ) * (k : ℝ)) ∧
    (∃ C : ℝ, ∀ T : ℕ → ℕ, SFMTime T →
      ∃ P : Program, Admissible P ∧
        ∀ (n m : ℕ) (f : Fin m → Finset (Fin n) → ℝ) (hf0 : ∀ i S, 0 ≤ f i S)
            (hsub : ∀ i, NonmonotoneSubmod.Shared.Submodular (f i))
            (hempty : ∀ i, f i ∅ = 0) (huniv : ∀ i, f i Finset.univ = 0)
            (k : ℕ), 1 ≤ k → k ≤ n → 1 ≤ m →
          ∃ (x : Fin n → LCField n k) (φ : LCField n k →ₗ[ZMod 2] BlockLabel k),
            Function.Injective x ∧ Function.Surjective φ ∧
            ∃ (t : ℕ) (s : State n), s = run P f [(n : ℤ), (m : ℤ), (k : ℤ)] t ∧
              s.halted = true ∧ (∀ i : Fin m, s.core.mem ((i : ℕ) : ℤ) = cardScore f k x φ i) ∧
              ∀ Teval : ℝ, 1 ≤ Teval →
                charged s Teval ≤ C * m * n ^ 3 * k * ((T n : ℕ) : ℝ) ^ 2 * (Teval + n)) ∧
    (∃ C' : ℝ, ∀ (n m : ℕ) (f : Fin m → Finset (Fin n) → ℝ) (hf0 : ∀ i S, 0 ≤ f i S)
        (hsub : ∀ i, NonmonotoneSubmod.Shared.Submodular (f i))
        (hempty : ∀ i, f i ∅ = 0) (huniv : ∀ i, f i Finset.univ = 0)
        (k : ℕ), 1 ≤ k → k ≤ n →
      ∀ (x : Fin n → LCField n k) (φ : LCField n k →ₗ[ZMod 2] BlockLabel k),
        Function.Injective x → Function.Surjective φ →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        1 - δ ≤ bernProb (sampleProb (cardScore f k x φ) (samplingScale n ε δ)) (fun ξ =>
          (∀ S : Finset (Fin n), S.card ≤ k →
            |∑ i, sampledWeight (cardScore f k x φ) (samplingScale n ε δ) ξ i * f i S -
                ∑ i, f i S| ≤ ε * ∑ i, f i S) ∧
          (supportCard (sampledWeight (cardScore f k x φ) (samplingScale n ε δ) ξ) : ℝ) ≤
            C' * (n : ℝ) * (k : ℝ) * ε⁻¹ ^ 2 * Real.log (2 * n / δ))) := by sorry

end SubmodSparsify.Supplement
