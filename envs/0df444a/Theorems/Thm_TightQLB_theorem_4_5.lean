-- Prove2me | Theorems.Thm_TightQLB_theorem_4_5
-- name    : TightQLB.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:04:08.910371+00:00
-- url     : https://prove2.me/theorems/ce503bf1-d2f3-4811-8b64-c7d8ba542d6c
-- title:
--   Theorem 4.5 — Fourier lower bound, $B(\mathcal A)\le3-\frac2N+\frac83\frac{q^{3/2}}{\sqrt N}+\frac{32}9(1-\frac1N)\frac{q^3}N$
-- statement:
--   Let $n\ge1$ and $N=2^n$, and let $\mathcal A$ be an algorithm that makes at most $q$ queries in the Fourier ensemble. Then
--
--   $$
--   B(\mathcal A)\le3-\frac2N+\frac83\cdot\frac{q^{3/2}}{\sqrt N}+\frac{32}9\Bigl(1-\frac1N\Bigr)\frac{q^3}N .
--   $$
--
--   Consequently, if $B(\mathcal A)\ge3+\varepsilon$ for some $0<\varepsilon\le4$, then
--
--   $$
--   q\ge(3\varepsilon/16)^{2/3}N^{1/3}.
--   $$
--
--   Since the honest one-query sampler scores exactly $3-2/N$, this shows that a device beating the ideal score by a constant must make $\Omega(N^{1/3})$ queries. It is the explicit form of part 1 of Theorem 1.1 of the paper.
--
--   **Formalization Note** The workspace `W` is any finite type, and the query register is `Qubits n × Bool`.
--
--   Differences from the source:
--   - reading: the operational experiment of Definition 3.1 (classical record, paths with at most q queries, ancillas, measurements, record-selected and record-controlled queries, output a function of the final record) → a density matrix on A × E, q + 1 oracle-independent CPTP maps on A, exactly q controlled queries on the fixed registers C × Q between them, and a POVM on A; reason: the proof of Lemma 3.2, Steps 1–2, puts every such experiment in this form, and conversely a CPTP map is an ancilla, a unitary and an ignored register and a POVM is a measurement of an ancilla, so the class is the same
--   - generalization: the score-only theorem, "the special case in which Eve's register is trivial" (p. 15) → every finite Eve register E and every joint initial state ρ_AE; reason: E = Unit is the source's statement, and the source's proof goes through for arbitrary E (§4 keeps E throughout: "which may be trivial")
--   - encoding: a sign function f : {0,1}^n → {−1, 1} and the oracle O_f → a bit function fb with f(x) = (−1)^(fb x), and QAlgorithms.xorOracle fb; reason: a bijection, and (1 − f(x))/2 = [fb x]
--   - encoding: Pr[Z = z | f] for the device → the real part of the trace of Tr_A[(M_z ⊗ I_E) ρ_final]; reason: the probability of outcome z under the POVM
--   - encoding: q^{3/2}, N^{1/3}, (3ε/16)^{2/3}, √N → Real.rpow and Real.sqrt, with q a natural number cast to ℝ; reason: Lean convention; same values
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), Theorem 4.5, p. 27 (PDF p. 30); the explicit form of Theorem 1.1 part 1, p. 2 (PDF p. 5)

import Mathlib
import Definitions.Def_TightQLB_Experiment

open QAlgorithms

namespace TightQLB

/-- **Theorem 4.5 (Fourier lower bound)**, p.27 (PDF p.30); the explicit form of part 1 of
Theorem 1.1, p.2 (PDF p.5).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"Let A be an algorithm that makes at most q queries in the Fourier ensemble. Then
B(A) ≤ 3 − 2/N + (8/3) · q^{3/2}/√N + (32/9)(1 − 1/N) q³/N. (35) Consequently, if B(A) ≥ 3 + ε for
some 0 < ε ≤ 4, then q ≥ (3ε/16)^{2/3} N^{1/3}."

**Formalization Note.**
* The algorithm is an experiment of Definition 3.1 in channel form (`TightQLB.Experiment`): an
  oracle-independent initial density matrix on `A × E`, `q + 1` oracle-independent CPTP rounds on `A`,
  `q` controlled value queries (query register `X × T = Qubits n × Bool`, oracle `valueOracle fb`)
  between them, and a POVM output. Fewer than `q` queries along a path
  are the control qubit set to `|0⟩`.
* Eve's register `E` is arbitrary (finite); the paper's score-only theorem is `E = Unit` ("the
  theorems about the score alone are the special case in which Eve's register is trivial", p.15).
  The workspace `W` is arbitrary (finite).
* `N = 2^n`; `q^{3/2}`, `N^{1/3}`, `(3ε/16)^{2/3}` are `Real.rpow`; `n ≥ 1` is the standing
  assumption of §3.1, p.13. -/
theorem theorem_4_5 {n q : ℕ} (hn : 1 ≤ n) {W E : Type} [Fintype W] [DecidableEq W]
    [Fintype E] [DecidableEq E] (A : Experiment n q (Qubits n × Bool) W E) :
    A.score ≤ 3 - 2 / (2 : ℝ) ^ n + 8 / 3 * (q : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt ((2 : ℝ) ^ n)
        + 32 / 9 * (1 - 1 / (2 : ℝ) ^ n) * (q : ℝ) ^ 3 / (2 : ℝ) ^ n ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 4 → 3 + ε ≤ A.score →
      (3 * ε / 16) ^ (2 / 3 : ℝ) * ((2 : ℝ) ^ n) ^ (1 / 3 : ℝ) ≤ (q : ℝ) := by sorry

end TightQLB
