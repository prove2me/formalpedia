-- Prove2me | Theorems.Thm_SchattenSketch_Main_theorem_1_1
-- name    : SchattenSketch.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:57:30.27653+00:00
-- url     : https://prove2.me/theorems/127bcc1a-9e7d-4da6-a505-f477925d950f
-- title:
--   Theorem 1.1 — the sketch dimension of the nuclear norm: $n^2/(\log n)^{A_\varepsilon}\le k_\varepsilon(n)\le C_\varepsilon n^2(\log\log(e^en))^2/\log(en)$
-- statement:
--   For $A\in\mathbb R^{n\times n}$ with singular values $\sigma_1(A)\ge\dots\ge\sigma_n(A)\ge 0$, the **nuclear norm** is $\|A\|_{S_1}=\sum_i\sigma_i(A)$. Let $k_\varepsilon(n)$ be the least integer $k\ge 0$ for which there is a randomized $k$-dimensional linear sketch $(S_\omega,d_\omega)$ — a random linear map $S_\omega:\mathbb R^{n\times n}\to\mathbb R^k$ chosen without seeing the input, followed by a measurable decoder $d_\omega$ that may depend on $\omega$ — such that for every fixed real $n\times n$ matrix $A$
--   $$P_\omega\bigl\{(1-\varepsilon)\|A\|_{S_1}\le d_\omega(S_\omega A)\le(1+\varepsilon)\|A\|_{S_1}\bigr\}\ge\tfrac23 .$$
--   **Theorem.** For every fixed $0<\varepsilon<1$ there are finite constants $A_\varepsilon,C_\varepsilon$, depending on $\varepsilon$ but not on $n$, such that for all sufficiently large $n$
--   $$\frac{n^2}{(\log n)^{A_\varepsilon}}\ \le\ k_\varepsilon(n)\ \le\ C_\varepsilon\,\frac{n^2\{\log\log(e^en)\}^2}{\log(en)} .$$
--   Logarithms are natural. The inputs are arbitrary real matrices, with no symmetry or positive-semidefiniteness promise (for positive semidefinite inputs one measurement, the trace, suffices).
--
--   The theorem settles, up to polylogarithmic factors, the linear-sketch dimension of the Schatten-1 norm, between the earlier $\Omega(n)$ lower bound and the trivial $O(n^2)$ upper bound: $n^{2-o(1)}$ measurements are necessary, and a factor of order $\log n/(\log\log n)^2$ can be saved over storing all entries.
--
--   **Formalization Note.** The least dimension is stated through its two defining properties: every valid sketch of dimension $k$ has $n^2/(\log n)^{A}\le k$, and some valid sketch has $k\le C\,n^2(\log\log(e^en))^2/\log(en)$. The sketch class is `LinearSketch n k` (seed space, measurable $S$, jointly measurable decoder) and validity is `IsValid nucNorm ε`. The threshold $N$ and the constants $A,C$ are chosen after $\varepsilon$ and before $n$, $k$ and the sketch.
--
--   Differences from the source:
--   - encoding: k_ε(n), the least k ≥ 0 admitting a valid sketch, with n²/(log n)^{A_ε} ≤ k_ε(n) ≤ C_ε n²{log log(e^e n)}²/log(en) → two conjuncts: every valid k-dimensional sketch has n²/(log n)^A ≤ k, and some valid sketch has k ≤ C n² (log log(e^e n))²/log(e n); reason: ℕ is well ordered, so the pair is exactly the two-sided bound on the least k; no ℕ-valued sInf (which would be 0 on an empty set)
--   - reading: a distribution of linear maps S_ω and measurable decoders d_ω (p. 4) → LinearSketch: seed space Ω : Type with a probability measure, S measurable in ω, decoder jointly measurable in (ω, y); reason: the paper's measurable decoders, with the joint measurability its Yao averaging (p. 35) and its measurable SVD convention (p. 31) use
--   - encoding: finite constants A_ε, C_ε; for all sufficiently large n → ∃ A C : ℝ, ∃ N : ℕ, ∀ n ≥ N; reason: the constants and threshold depend on ε only
--   - encoding: natural log, (log n)^{A_ε}, log log(e^e n), log(en) → Real.log, Real.rpow, Real.log (Real.log (Real.exp (Real.exp 1) * n)), Real.log (Real.exp 1 * n); reason: notation
--   - encoding: S_ω : R^{n×n} → R^k linear; probability ≥ 2/3 → S ω : Fin k → Fin n × Fin n → ℝ applied by sketchApply; (2/3 : ℝ≥0∞) ≤ P {…}; reason: a linear map is its k × n² matrix; probabilities in ℝ≥0∞
--   - encoding: singular values σ_1 ≥ … ≥ σ_n of A, ‖A‖_{S₁} = Σ σ_i(A) → published singVal (0-based: σ_i = singVal (i - 1)) and nucNorm = Σ_{j<n} singVal j A; reason: Lean indexing; same quantities
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 5, Theorem 1.1, (1.2) (model and k_ε(n): p. 4, (1.1))

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_SchattenSketch_Main_Sketch

open WainwrightHDS.NucNorm

namespace SchattenSketch.Main

/-- Theorem 1.1 (Yang, arXiv:2608.22247, p. 5), both halves of (1.2). For every `0 < ε < 1` there
are constants `A, C` and a threshold `N` such that for all `n ≥ N`:
every `(1 ± ε)`-valid randomized `k`-dimensional linear sketch of the nuclear norm on `ℝ^{n×n}`
has `n² / (log n)^A ≤ k`; and some `(1 ± ε)`-valid sketch has
`k ≤ C n² (log log(e^e n))² / log(e n)`. -/
theorem theorem_1_1 :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ A C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∀ (k : ℕ) (sk : LinearSketch n k), sk.IsValid nucNorm ε →
            (n : ℝ) ^ 2 / Real.log n ^ A ≤ k) ∧
        (∃ (k : ℕ) (sk : LinearSketch n k), sk.IsValid nucNorm ε ∧
            (k : ℝ) ≤ C * (n : ℝ) ^ 2 *
              Real.log (Real.log (Real.exp (Real.exp 1) * n)) ^ 2 / Real.log (Real.exp 1 * n)) := by sorry

end SchattenSketch.Main
