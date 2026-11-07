-- Prove2me | Theorems.Thm_QuarticGap_theorem_4_3
-- name    : QuarticGap.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:53.817995+00:00
-- url     : https://prove2.me/theorems/ea93b390-356b-4c25-9e8d-b896a898e5ee
-- title:
--   Theorem 4.3 — sampling from well-conditioned linear systems takes $\Omega(n^2/\log n)$ classical but $\Theta(\sqrt n)$ quantum queries
-- statement:
--   Fix rational $\lambda \in (0,1]$ and $\alpha \in (0,1/(1+8\lambda)]$, and put
--   $$
--   \varepsilon_{\mathrm{lin}}(\lambda,\alpha) = \min\Bigl\{\frac{\lambda^2}{\sqrt e\,(3+\alpha^2+2\lambda^2+\lambda^4)},\ \frac{\lambda^2}{3+\alpha^2+5\lambda^2+2\lambda^4}\Bigr\}.
--   $$
--   Consider the family $\{\widehat A_W : W \in \mathcal G\}$ with right-hand side $\widehat b$, for powers of four $n$. For every constant $\varepsilon \in (0,\varepsilon_{\mathrm{lin}}(\lambda,\alpha))$, there are $c > 0$ and $n_0$ such that, for every $n \ge n_0$:
--
--   1. every classical algorithm that samples from $p_{\widehat A_W^{-1}\widehat b}$ within total variation distance $\varepsilon$ for every $W \in \mathcal G$ makes more than $cn^2/\log n$ queries on some $W \in \mathcal G$, and more than $cn^2/\log n$ queries in expectation on some $W \in \mathcal G$; querying all $n^2$ unknown entries suffices to sample exactly;
--   2. a quantum algorithm samples within total variation distance $\varepsilon$ with $O(\sqrt n)$ queries and $\widetilde O(\sqrt n)$ gates, and every quantum algorithm that does so makes $\Omega(\sqrt n)$ queries on some $W \in \mathcal G$.
--
--   Since $\rho(\widehat A_W)^2 = \Theta(n)$ and the condition number is constant, the classical and quantum query complexities are $\widetilde\Theta(\rho^4)$ and $\Theta(\rho)$. So the fourth-power dependence of dequantized solvers on $\rho$ is tight up to a logarithmic factor.
--
--   **Formalization Note** $n = 4^\ell$. The constants $c$, $C$, $n_0$ come before the algorithm. Classical algorithms are `QueryAlg` against $\mathrm{SQ}(\widehat A_W)$. The upper bound is one circuit over $\{H,T,\mathrm{CNOT}\}$ that works for every legal choice of the operations, with an output that reads $2+2\ell$ wires; the lower bound is over all circuits with arbitrary unitary gates and output maps. The last clause gives the values of Lemma 4.1, from which $\rho^2 = \Theta(n)$ follows.
--
--   Differences from the source:
--   - encoding: n a power of four, indices {0,1}^k → n = 4^ℓ, k = 2ℓ, √n = 2^ℓ; reason: the same values of n
--   - reading: a randomized classical algorithm → QueryAlg, a behaviour strategy on transcripts with unrestricted computation; reason: an algorithm with private coins has perfect recall, so Kuhn gives the same law; the input reaches it only through the answers
--   - encoding: output distribution within total variation distance ε → sampleErr, which counts the mass of non-halting runs as an extra outcome; reason: it is TV for an algorithm that halts almost surely, and gives a non-halting algorithm no advantage
--   - reading: a quantum algorithm → an oracle circuit on any number of wires, started in |0⟩ and measured at the end; for each n one circuit, with no uniformity condition; reason: measurements can be deferred since Definition 2.2 grants controlled versions; the source claims no uniformity
--   - reading: Õ(√n) gates → at most C√n(log n)^C gates from {H, T, CNOT}, query calls not counted, with the output reading designated wires; reason: the proof synthesizes rotations over a finite universal gate set, of which this is the strongest natural choice
--   - reading: a fixed binary encoding of the entries → a sign bit and numerator and denominator in ℓ + B(λ, α) bits each; reason: p.17 says that numerators and denominators have O(log n) bits, and Lemma 2.7 says the choice affects only constant factors
--   - encoding: conditional sampling in a zero row or column returns a fixed index → the fixed index is default; reason: Â_W has no zero row or column, so it is never returned
--   - encoding: since ρ(Â_W)² = Θ(n), the complexities are Θ̃(ρ⁴) and Θ(ρ) → a clause with ∥Â_W∥ = 1, the condition-number bound and ρ(Â_W)² = n(1 + α²(3 + 2λ²)) on G; reason: with the bounds in n, these values are the content of the sentence
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Theorem 4.3, pp.30–31

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QuarticGap_Ahat

open QAlgorithms

namespace QuarticGap

/-- Theorem 4.3 (Chakrabarti, Herman, Kim, Ozgul, *The Quartic Gap Between Quantum and Dequantized
Algorithms for Linear Algebra Is Tight*, arXiv:2610.42069 (file sha256 9f68aaf9…), pp.30–31). Fix
rational `λ ∈ (0, 1]`, `α ∈ (0, 1/(1 + 8λ)]`. For every constant `ε ∈ (0, ε_lin(λ, α))` there are
`c > 0` and `n₀` such that, for every power of four `n ≥ n₀`:

1. Every classical algorithm that samples from `p_{Â_W⁻¹b̂}` within `ε` for every `W ∈ G` makes more than
   `cn²/log n` queries on some `W ∈ G`, and more than `cn²/log n` in expectation on some `W ∈ G`. Querying
   all `n²` unknown entries suffices to sample exactly.
2. A quantum algorithm samples within `ε` with `O(√n)` queries and `Õ(√n)` gates, and every quantum
   algorithm that does so makes `Ω(√n)` queries on some `W ∈ G`.

Since `ρ(Â_W)² = Θ(n)`, the classical and quantum query complexities are `Θ̃(ρ⁴)` and `Θ(ρ)`.

**Formalization Note** `n = 4^ℓ`, `lam` is `λ`. Classical algorithms are `QueryAlg` against `SQ(Â_W)`
(Definition 2.1), adaptive and randomized, with unrestricted computation; `c`, `C`, `n₀` come before
the algorithm. A quantum algorithm is an `OracleCircuit` on any number of wires, started in `|0⟩` and
measured at the end. In the upper bound it is one circuit over `{H, T, CNOT}` that works for every
legal choice of the operations (Definition 2.2), with an output that reads wires, and `Õ(√n)` is
`C√n(log n)^C`. In the lower bound it is any circuit over all unitary gates with any output map, and
the gates are fixed before the oracles, so a fixed query count is "on some `W`". The exact sampler
asks only entry queries at the `n²` unknown positions (row `n + a`, column `b`). The last clause
carries the closing sentence, with the values of Lemma 4.1. -/
theorem theorem_4_3 (lam α : ℚ) (hlam : 0 < lam ∧ lam ≤ 1) (hα : 0 < α ∧ α ≤ 1 / (1 + 8 * lam))
    (ε : ℝ) (hε : 0 < ε ∧ ε < εLin lam α) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ ℓ : ℕ, n₀ ≤ 4 ^ ℓ →
      (∀ alg : QueryAlg (SQQuery (Idx ℓ) (Idx ℓ)) (SQAns (Idx ℓ) (Idx ℓ)) (Idx ℓ),
        (∀ W ∈ G ℓ, alg.sampleErr (famRespond lam α W) (target lam α W) ≤ ε) →
        (∃ W ∈ G ℓ, ¬ alg.MakesAtMostReal (famRespond lam α W)
          (c * ((4 : ℝ) ^ ℓ) ^ 2 / Real.log ((4 : ℝ) ^ ℓ))) ∧
        (∃ W ∈ G ℓ, ENNReal.ofReal (c * ((4 : ℝ) ^ ℓ) ^ 2 / Real.log ((4 : ℝ) ^ ℓ)) <
          alg.expQueries (famRespond lam α W))) ∧
      (∃ alg : QueryAlg (SQQuery (Idx ℓ) (Idx ℓ)) (SQAns (Idx ℓ) (Idx ℓ)) (Idx ℓ),
        (∀ tr q, alg.step tr (Sum.inl q) ≠ 0 →
          ∃ i j : Idx ℓ, blk i = 1 ∧ blk j = 0 ∧ q = SQQuery.entry i j) ∧
        ∀ W ∈ G ℓ, alg.MakesAtMost (famRespond lam α W) ((4 ^ ℓ) ^ 2) ∧
          alg.sampleErr (famRespond lam α W) (target lam α W) = 0) ∧
      (∃ (N : ℕ) (alg : OracleCircuit htcxGateSet (famArity ℓ lam α) N)
          (w : Fin (2 + 2 * ℓ) ↪ Fin N),
        (totalQueries alg : ℝ) ≤ C * Real.sqrt ((4 : ℝ) ^ ℓ) ∧
        (alg.gateCount : ℝ) ≤ C * Real.sqrt ((4 : ℝ) ^ ℓ) * Real.log ((4 : ℝ) ^ ℓ) ^ C ∧
        ∀ W ∈ G ℓ, ∀ orc, IsFamAccess lam α W orc →
          tv (qOut alg orc (readWires w)) (target lam α W) ≤ ε) ∧
      (∀ (N : ℕ) (alg : OracleCircuit UnitaryGates (famArity ℓ lam α) N) (out : Qubits N → Idx ℓ),
        (∀ W ∈ G ℓ, ∀ orc, IsFamAccess lam α W orc →
          tv (qOut alg orc out) (target lam α W) ≤ ε) →
        c * Real.sqrt ((4 : ℝ) ^ ℓ) ≤ totalQueries alg) ∧
      (∀ W ∈ G ℓ,
        specNorm (Ahat lam α W) = 1 ∧
        specNorm (Ahat lam α W) * specNorm (Ahat lam α W)⁻¹ ≤
          (1 + 8 * (lam : ℝ) + 8 * (lam : ℝ) ^ 2) / α ∧
        rho (Ahat lam α W) ^ 2 = 4 ^ ℓ * (1 + (α : ℝ) ^ 2 * (3 + 2 * (lam : ℝ) ^ 2))) := by sorry

end QuarticGap
