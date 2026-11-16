-- Prove2me | Theorems.Thm_QuarticGap_Supplement_theorem_5_9
-- name    : QuarticGap.Supplement.theorem_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:57:41.403895+00:00
-- url     : https://prove2.me/theorems/9fefa196-8ffe-4d79-98bf-2f1dcfb64129
-- title:
--   Theorem 5.9 — top principal component and rank-one truncation of $G_W$: $\Omega(n^2/\log n)$ classical, $\widetilde\Theta(\sqrt n)$ quantum
-- statement:
--   Fix a rational number $t \in (0,1/64]$ and the family $G_W = I + \varphi\varphi^{\mathsf T} + t\widetilde T_W$ of (22). For every constant $\varepsilon \in (0, t^4/8)$ there are $c > 0$, $C > 0$ and $n_0$ such that, for every power of four $n \ge n_0$, each of the following tasks on $\{G_W : W \in \mathcal G\}$
--
--   1. sampling from $p_{w_W}$ within total variation distance $\varepsilon$, where $w_W$ is the top principal component;
--   2. sampling within total variation distance $\varepsilon$ from the squared entries of row $0$ of the rank-one spectral truncation $(G_W)_{\ge 3/2}$;
--
--   requires more than $cn^2/\log n$ classical queries (access $\mathrm{SQ}(G_W)$) on some input, both in the worst case and in expectation, can be solved by a quantum algorithm with at most $C\sqrt n(\log n)^C$ queries, and requires at least $c\sqrt n$ quantum queries.
--
--   Moreover, there is $\delta > 0$ such that, for every $n$ and every $W \in \mathcal G$:
--   $$
--   (G_W)_{\ge3/2} = \lambda_1 w_Ww_W^{\mathsf T},\qquad \bigl\|\text{row }0\text{ of }(G_W)_{\ge3/2}\bigr\| \ge 1,\qquad \bigl\|\text{row }0\text{ of }G_W\bigr\| = \sqrt{5/2},
--   $$
--   and $|\lambda - 3/2| \ge \delta$ for every eigenvalue $\lambda$ of $G_W$. The requested row is fixed independently of $W$.
--
--   These facts show the second task is not degenerate: an error small relative to the original row is small relative to the truncated row, and the truncation is stable under small perturbations.
--
--   **Formalization Note** The adjoined coordinate $0$ is `none`; in the padded register it sits at position $0$ of the fourth block. $(G_W)_{\ge3/2}$ is defined spectrally.
--
--   Differences from the source:
--   - encoding: n a power of four, positions in {0,1}^k → n = 4^ℓ, positions in {0,1}^{2ℓ}, √n = 2^ℓ; reason: the same values of n
--   - reading: a randomized classical algorithm → QueryAlg, a behaviour strategy on transcripts with unrestricted computation; reason: an algorithm with private coins and perfect recall has a behaviour strategy with the same law (Kuhn); the input reaches it only through the answers
--   - encoding: output distribution within total variation distance ε → sampleErr, which counts the mass of non-halting runs as an extra outcome; reason: it is TV for an algorithm that halts almost surely and gives a non-halting algorithm no advantage
--   - encoding: coherent access to the 3n × 3n (or (3n+1) × (3n+1)) matrix → coherent access to the matrix zero padded to 4n × 4n, quantum outputs in the 4n padded coordinates with the target padded by zeros; reason: Remark 4.4 (p.32): the padded rows and columns are zero and known and the targets vanish on them; an output on a padding coordinate only adds error
--   - reading: a fixed binary encoding of the entries → the published ratEnc: sign bit, numerator and denominator in 2ℓ + 2 + size(|num t|·den t) bits; reason: every entry is rational with numerator and denominator of O(log n) bits (§2.4, p.17); the width fits all of them exactly
--   - reading: a quantum algorithm → an oracle circuit on any number of wires, started in |0⟩ and measured at the end, fixed before W and the oracles and correct for every legal choice of the input operations; reason: Definition 2.2: an algorithm must succeed for every choice of the unspecified action; the base goal's convention
--   - reading: quantum query complexity Θ̃(√n) → one circuit over all unitary gates with at most C√n(log n)^C queries, output reading wires, and at least c√n queries for every circuit over all unitary gates with any output map; reason: the proof's Lemma 2.10 gives Ω(√n) and §5 (p.33) says Θ̃(ρ) queries suffice and are necessary; the stronger reading of the lower bound
--   - encoding: λ₁, the unit eigenvector w_W with φᵀw_W > 0, and the truncation (G_W)_{≥3/2} → sSup of the real spectrum; a chosen vector with these properties (0 if none); the continuous functional calculus of x ↦ x·1[x ≥ 3/2]; reason: for W ∈ G the vector is unique (Lemmas 5.7, 5.8) and only W ∈ G is used; the truncation keeps exactly the eigenvalues ≥ 3/2
--   - reading: the requested row is fixed independently of W → not a conjunct: the task reads row none by definition; reason: it holds by construction
--   - reading: the closing sentences on the row norms and the eigenvalue distance → stated for every n and every W ∈ G, with one δ > 0 uniform in n and W; reason: Lemmas 5.7 and 5.8 hold for every W ∈ G; the stronger of the two readings (not only n ≥ n₀)
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Theorem 5.9 with (22), pp.38–39

import Mathlib
import Definitions.Def_QuarticGap_Supplement_Gmat

open QAlgorithms

namespace QuarticGap.Supplement

/-- Theorem 5.9 (arXiv:2610.42069 (file sha256 9f68aaf9…), p.39). Fix a rational number
`t ∈ (0, 1/64]`. For every constant `ε ∈ (0, t⁴/8)`, there are `c > 0` and `n₀` such that, for every
power of four `n ≥ n₀`, each of the following tasks on `{G_W : W ∈ G}` requires more than
`cn²/log n` classical queries on some input, both in the worst case and in expectation, and has
quantum query complexity `Θ̃(√n)`:
1. sampling from `p_{w_W}` within total variation distance `ε`, where `w_W` is the top principal
   component;
2. sampling within total variation distance `ε` from the squared entries of row `0` of the rank-one
   spectral truncation `(G_W)_{≥3/2} = λ₁w_Ww_Wᵀ`.
The requested row is fixed independently of `W`. Its norm after truncation is at least one, its norm
in `G_W` is `√(5/2)`, and the threshold `3/2` has a constant distance from every eigenvalue.

**Formalization Note** `n = 4^ℓ`; the adjoined coordinate `0` is `none`. The models are those of the
published goal: classical `QueryAlg` against `SQ(G_W)` on the `(3n + 1) × (3n + 1)` matrix; quantum
circuits with access to `G_W` zero padded to `4n × 4n` (Remark 4.4), the adjoined coordinate sitting
at position `0` of the fourth block. "Quantum query complexity `Θ̃(√n)`" is read as for Theorem 5.6:
an upper bound of `C√n(log n)^C` queries by one circuit over all unitary gates fixed before `W` and
the oracles, and a lower bound of `c√n` queries for every circuit; no gate clause. `(G_W)_{≥3/2}` is
defined spectrally, and its identity with `λ₁w_Ww_Wᵀ` is a conclusion. That row `0` is fixed
independently of `W` holds by definition (`pcVec .row0` reads row `none`). The remaining closing facts
are stated for every `W ∈ G` and every `n`, with one `δ > 0` for the eigenvalue distance, uniform in
`n` and `W`. -/
theorem theorem_5_9 (t : ℚ) (ht : 0 < t ∧ t ≤ 1 / 64) (ε : ℝ) (hε : 0 < ε ∧ ε < (t : ℝ) ^ 4 / 8) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ ℓ : ℕ, n₀ ≤ 4 ^ ℓ → ∀ task : PCTask,
      (∀ alg : QueryAlg (SQQuery (IxG ℓ) (IxG ℓ)) (SQAns (IxG ℓ) (IxG ℓ)) (IxG ℓ),
        (∀ W ∈ G ℓ, alg.sampleErr (gRespond t W) (lenSqDist (pcVec task t W)) ≤ ε) →
        (∃ W ∈ G ℓ, ¬ alg.MakesAtMostReal (gRespond t W)
          (c * ((4 : ℝ) ^ ℓ) ^ 2 / Real.log ((4 : ℝ) ^ ℓ))) ∧
        (∃ W ∈ G ℓ, ENNReal.ofReal (c * ((4 : ℝ) ^ ℓ) ^ 2 / Real.log ((4 : ℝ) ^ ℓ)) <
          alg.expQueries (gRespond t W))) ∧
      (∃ (N : ℕ) (alg : OracleCircuit UnitaryGates (supArity ℓ t) N)
          (w : Fin (2 + 2 * ℓ) ↪ Fin N),
        (totalQueries alg : ℝ) ≤ C * Real.sqrt ((4 : ℝ) ^ ℓ) * Real.log ((4 : ℝ) ^ ℓ) ^ C ∧
        ∀ W ∈ G ℓ, ∀ orc, IsGAccess t W orc →
          tv (qOut alg orc (readWires w)) (lenSqDist (padVec decG (pcVec task t W))) ≤ ε) ∧
      (∀ (N : ℕ) (alg : OracleCircuit UnitaryGates (supArity ℓ t) N) (out : Qubits N → Idx ℓ),
        (∀ W ∈ G ℓ, ∀ orc, IsGAccess t W orc →
          tv (qOut alg orc out) (lenSqDist (padVec decG (pcVec task t W))) ≤ ε) →
        c * Real.sqrt ((4 : ℝ) ^ ℓ) ≤ totalQueries alg)) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ ℓ : ℕ, ∀ W ∈ G ℓ,
      truncG t W = lam1 t W • Matrix.vecMulVec (topPC t W) (topPC t W) ∧
      1 ≤ rowNorm (truncG t W) none ∧
      rowNorm (Gmat t W) none = Real.sqrt (5 / 2) ∧
      ∀ x ∈ spectrum ℝ (Gmat t W), δ ≤ |x - 3 / 2| := by sorry

end QuarticGap.Supplement
