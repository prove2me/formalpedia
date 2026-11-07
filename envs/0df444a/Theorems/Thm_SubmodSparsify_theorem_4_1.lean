-- Prove2me | Theorems.Thm_SubmodSparsify_theorem_4_1
-- name    : SubmodSparsify.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:21.24035+00:00
-- url     : https://prove2.me/theorems/a610c56a-cb4e-465d-89d8-c8292d151b7f
-- title:
--   Theorem 4.1 — Algorithm 1's weights give $\varepsilon$-sparsifiers of size $O(\varepsilon^{-2}n^2\log(2n/\delta))$ in time $O(mn^3T_{\min}(n)^2(T_{\mathrm{eval}}+n))$
-- statement:
--   Let $F = \sum_{i=1}^m f_i$ be the sum of nonnegative submodular functions $f_1, \dots, f_m : 2^{[n]} \to \mathbb R_{\ge 0}$ with $f_i(\emptyset) = f_i([n]) = 0$, and let $p_1, \dots, p_m$ be the sampling weights of Algorithm 1 (shares of the $2n$ terminal decompositions).
--
--   1. **Weights.** $p_i \ge 0$ for all $i$, and $\sum_{i=1}^m p_i \le 2n(n-1)$.
--   2. **Time.** Algorithm 1 (with Algorithm 2 as a subroutine) computes $p_1, \dots, p_m$ deterministically in time
--   $$O\bigl(m n^3 T_{\min}(n)^2 (T_{\mathrm{eval}} + n)\bigr):$$
--   there is an absolute constant $C$ such that for every time bound $T$ of submodular minimization there is one deterministic program on the $m$-oracle RAM that, for all $n, m \ge 1$ and $f_1, \dots, f_m$ as above, halts with $p_i$ in output cell $i$ in time at most $C\, m\, n^3\, T(n)^2 (T_{\mathrm{eval}} + n)$ whenever each oracle query costs $T_{\mathrm{eval}} \ge 1$.
--   3. **Sparsification.** There is an absolute constant $C'$ such that for all $\varepsilon, \delta \in (0,1)$, with $\Lambda := 56\varepsilon^{-2}\log(32n/\delta)$ and independent sampling of each $f_i$ with probability $\min\{1, \Lambda p_i\}$ and weight $w_i = 1/\min\{1, \Lambda p_i\}$ (else $w_i = 0$), with probability at least $1 - \delta$ the reweighted sum $\tilde F := \sum_i w_i f_i$ satisfies both
--   $$|\tilde F(S) - F(S)| \le \varepsilon F(S) \ \text{ for all } S \subseteq [n] \qquad \text{and} \qquad |\mathrm{supp}(w)| \le C' \varepsilon^{-2} n^2 \log(2n/\delta).$$
--
--   This gives sparsifiers of near-quadratic size $O(\varepsilon^{-2} n^2 \log(2n/\delta))$ for sums of arbitrary nonnegative submodular functions, matching the $\Omega(n^2)$ lower bound for directed cuts up to the logarithm.
--
--   Differences from the source:
--   - encoding: ground set [n] = {1, …, n}, subsets of [n], components f_1, …, f_m → Fin n (paper index = value + 1), Finset (Fin n), f : Fin m → Finset (Fin n) → ℝ; reason: Lean representation; same instances
--   - encoding: "Algorithm 1 computes nonnegative sampling weights p_1, …, p_m" → weights f, the shares of (15) on the 2n terminal families (definition SubmodSparsify.weights), which the program must output exactly; reason: the theorem is about Algorithm 1's weights; Algorithm 2 computes (15) exactly (Claim 4.3)
--   - encoding: Σ_i p_i = O(n²) (specifically Σ_i p_i ≤ 2n(n − 1)) → Σ_i p_i ≤ 2n(n − 1) with real subtraction; reason: the explicit bound implies the O(n²) one
--   - reading: running time O(·) in terms of Tmin(n), the time complexity of submodular minimization → ∃ C, ∀ T with SFMTime T (one FasterSFM program minimizes every submodular function on Fin n within T(n) steps), ∃ program with time ≤ C·(…)·T(n)²·(Teval + n); reason: Tmin(n) is any achievable SFM time bound; the constant C is absolute, chosen before T and the program (the stronger reading of O(·))
--   - encoding: "deterministic time", value-oracle queries costing Teval → a coin-free program of the m-oracle RAM SubmodSparsify.Machine; time = (work − queries) + Teval·queries, bounded for every real Teval ≥ 1; reason: the paper's cost model: queries at Teval, other operations at unit cost
--   - encoding: O(·) over instances → n ≥ 1 and m ≥ 1; reason: the bound concerns nonempty instances; at m = 0 the right-hand side is 0 while halting costs one step
--   - encoding: the algorithm outputs the weights → input [n, m] (or [n, m, u, dir]) in integer memory; the program halts with the i-th value in real-memory cell i; reason: a fixed input/output layout of the RAM; the f_i are reachable only through query
--   - reading: "with probability at least 1−δ, F̃ is an ε-sparsifier of F … with sparsity |supp(w)| = O(ε⁻²n² log(2n/δ))" → one event containing both properties, with |supp(w)| ≤ C′ε⁻²n² log(2n/δ) for one absolute C′ chosen before n, m, f, ε, δ; reason: the sentence asserts both properties on the same event; the O(·) constant is absolute
--   - encoding: Bernoulli sampling, weights w_i, |supp(w)|, natural log → bernProb with q_i = sampleProb, sampledWeight, supportCard (definition SubmodSparsify.bernProb); Λ = samplingScale n ε δ; Real.log; reason: the finite product law of the independent draws; same distribution
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), Theorem 4.1, p.18 (PDF p.20); Algorithm 1, p.18 (PDF p.20); proof, §4.3, pp.26–28 (PDF pp.28–30)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubmodSparsify_weights
import Definitions.Def_SubmodSparsify_bernProb
import Definitions.Def_SubmodSparsify_Machine
import Definitions.Def_SubmodSparsify_SFMTime

namespace SubmodSparsify

/-- **Theorem 4.1** (p.18): importance sampling with Algorithm 1's weights gives `ε`-sparsifiers of
size `O(ε⁻²n² log(2n/δ))`.

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Theorem 4.1, p.18; Algorithm 1, p.18.

Let `F = Σᵢ fᵢ` with `f₁, …, f_m : {0,1}ⁿ → R≥0` nonnegative submodular, `fᵢ(∅) = fᵢ([n]) = 0`.
(a) Algorithm 1's sampling weights `pᵢ` are nonnegative with `Σᵢ pᵢ ≤ 2n(n − 1)`.
(b) They are computed deterministically in time `O(mn³Tmin(n)²(Teval + n))`.
(c) For `ε, δ ∈ (0, 1)` and `Λ := 56ε⁻² log(32n/δ)`, sampling each `fᵢ` independently with
probability `min{1, Λpᵢ}` and weight `wᵢ = 1/min{1, Λpᵢ}` (else `wᵢ = 0`), with probability at
least `1 − δ` the reweighted sum `F̃ = Σᵢ wᵢfᵢ` satisfies `|F̃(S) − F(S)| ≤ εF(S)` for all `S ⊆ [n]`
and `|supp(w)| ≤ C′ε⁻²n² log(2n/δ)`, for one absolute constant `C′`.

**Formalization Note.** `[n]` is `Fin n`, components `f : Fin m → Finset (Fin n) → ℝ` (paper
indices = values + 1). `weights f` are the weights of Algorithm 1 defined by (14)–(15) on the `2n`
terminal families (module `SubmodSparsify.weights`). `SFMTime T` says that one admissible program of the published value-oracle RAM
`FasterSFM.Machine` minimizes every submodular function on an `n`-element ground set within
`T n` steps (`Tmin(n) ≤ T(n)`). Algorithm 1 runs on the deterministic `m`-oracle RAM of module
`SubmodSparsify.Machine`; `charged s Teval` is its running time when each value query to an
`fᵢ` costs `Teval` and every other instruction costs `1`. The program is one finite list for all
`n`, `m`, `f`; the `fᵢ` are reachable only through `query`. `O(·)` is an absolute constant `C`,
chosen before the SFM time bound `T` and the program; `n, m ≥ 1` (the bound concerns nonempty
instances). The program halts with `pᵢ` in
real-memory cell `i`. In (c) the sample `ξ`, its product Bernoulli law `bernProb`, the weights
`sampledWeight` and `|supp(w)| = supportCard` are those of module `SubmodSparsify.bernProb`;
`Λ = samplingScale n ε δ`; both properties hold on one event; `C′` is chosen before `n`, `m`, `f`,
`ε`, `δ`. Logarithms are natural. -/
theorem theorem_4_1 :
    (∀ (n m : ℕ) (f : Fin m → Finset (Fin n) → ℝ) (hf0 : ∀ i S, 0 ≤ f i S)
        (hsub : ∀ i, NonmonotoneSubmod.Shared.Submodular (f i))
        (hempty : ∀ i, f i ∅ = 0) (huniv : ∀ i, f i Finset.univ = 0),
      (∀ i, 0 ≤ weights f i) ∧ ∑ i, weights f i ≤ 2 * (n : ℝ) * ((n : ℝ) - 1)) ∧
    (∃ C : ℝ, ∀ T : ℕ → ℕ, SFMTime T →
      ∃ P : Program, Admissible P ∧
        ∀ (n m : ℕ) (f : Fin m → Finset (Fin n) → ℝ) (hf0 : ∀ i S, 0 ≤ f i S)
            (hsub : ∀ i, NonmonotoneSubmod.Shared.Submodular (f i))
            (hempty : ∀ i, f i ∅ = 0) (huniv : ∀ i, f i Finset.univ = 0),
          1 ≤ n → 1 ≤ m → ∃ (t : ℕ) (s : State n), s = run P f [(n : ℤ), (m : ℤ)] t ∧
            s.halted = true ∧ (∀ i : Fin m, s.core.mem ((i : ℕ) : ℤ) = weights f i) ∧
            ∀ Teval : ℝ, 1 ≤ Teval →
              charged s Teval ≤ C * m * n ^ 3 * ((T n : ℕ) : ℝ) ^ 2 * (Teval + n)) ∧
    (∃ C' : ℝ, ∀ (n m : ℕ) (f : Fin m → Finset (Fin n) → ℝ) (hf0 : ∀ i S, 0 ≤ f i S)
        (hsub : ∀ i, NonmonotoneSubmod.Shared.Submodular (f i))
        (hempty : ∀ i, f i ∅ = 0) (huniv : ∀ i, f i Finset.univ = 0),
      ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        1 - δ ≤ bernProb (sampleProb (weights f) (samplingScale n ε δ)) (fun ξ =>
          (∀ S : Finset (Fin n),
            |∑ i, sampledWeight (weights f) (samplingScale n ε δ) ξ i * f i S - ∑ i, f i S| ≤
              ε * ∑ i, f i S) ∧
          (supportCard (sampledWeight (weights f) (samplingScale n ε δ) ξ) : ℝ) ≤
            C' * ε⁻¹ ^ 2 * (n : ℝ) ^ 2 * Real.log (2 * n / δ))) := by sorry

end SubmodSparsify
