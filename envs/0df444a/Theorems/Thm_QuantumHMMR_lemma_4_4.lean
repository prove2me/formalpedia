-- Prove2me | Theorems.Thm_QuantumHMMR_lemma_4_4
-- name    : QuantumHMMR.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:39:29.035212+00:00
-- url     : https://prove2.me/theorems/fa1084be-cc09-49e0-a708-ed4356ca20aa
-- title:
--   Lemma 4.4 — a uniform test on $12h + 10$ copies for states with many stabilizers
-- statement:
--   For $19 \le h \le n - 2$, a uniform polynomial-time test using $12h + 10$ copies accepts every pure state $\psi$ with $\dim S(\psi) \ge n - h$ with probability at least $5/8$, and accepts a Haar-random state with probability at most $1/2 + 2^{-\Omega(n)}$.
--
--   The test is the Bell-difference test of [BL26, Theorem 2 and Supplement, proof of Theorem 4]. It takes $3h + 2$ Bell-difference samples (four copies each) and computes the subspace of their span commuting with all samples. If this subspace is nontrivial, it selects a uniformly random nonidentity Pauli from it, measures that Pauli on two fresh copies and accepts if the two outcomes agree; otherwise it outputs a fair bit. This uses $4(3h + 2) + 2 = 12h + 10$ copies, with binary linear algebra for the classical processing.
--
--   Formally: there is a uniform polynomial-time family $D'(n, h)$ of copy tests with exactly $12h + 10$ copies such that the acceptance probability on $\psi^{\otimes(12h+10)}$ is at least $5/8$ whenever $\psi$ is a unit vector with $\dim S(\psi) \ge n - h$, and there are $c > 0$ and $n_0$ with
--   $$
--   \mathop{\mathbb E}_{U \sim \mu_H} \Pr[D'(n,h) \text{ accepts } U|0^n\rangle] \le \tfrac12 + 2^{-cn} \qquad (n \ge n_0,\ 19 \le h \le n-2).
--   $$
--
--   This lemma supplies the distinguisher of Theorem 1.3.
--
--   Differences from the source:
--   - encoding: a uniform polynomial-time test → IsUniformFamily of CopyTest circuits (gates H, T, CNOT, CRot; measurements deferred to one output wire), the index (n, h) given as 1ⁿ0 1ʰ; reason: the QPT model of p.11 fixes no gate set; the exact uniform choice of the test needs CRot
--   - reading: 1/2 + 2^{−Ω(n)} → ∃ c > 0, n₀ with acceptance ≤ 1/2 + 2^{−cn} for n ≥ n₀, uniformly in h; reason: the standard meaning of Ω; uniformity in h is the stronger reading
--   - encoding: a Haar-random state; a pure state → U|0ⁿ⟩ with U ∼ haarLaw n; a unit vector (IsState); reason: the same objects
--   - generalization: a test using 12h + 10 copies for 19 ≤ h ≤ n − 2 → (D′ (n, h)).K = 12h + 10 for every (n, h); reason: outside the range the family may be any test with that many copies, so the page's family gives one; inside the range it is the page's count
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Lemma 4.4, p.14

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
import Definitions.Def_QuantumHMMR_CopyTest
import Definitions.Def_QuantumHMMR_IsUniformFamily
import Definitions.Def_QuantumHMMR_stabDim

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory

namespace QuantumHMMR

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

/-- **Lemma 4.4** (testing states with many stabilizers; Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), p.14, the Bell-difference test of
[BL26, Theorem 2 and Supplement, proof of Theorem 4]). For `19 ≤ h ≤ n - 2`, a uniform
polynomial-time test using `12h + 10` copies accepts every pure state `ψ` with
`dim S(ψ) ≥ n - h` with probability at least `5/8`, and accepts a Haar-random state with
probability at most `1/2 + 2^{-Ω(n)}`.

The test takes `3h + 2` Bell-difference samples (four copies each) and computes the subspace of
their span commuting with all samples. If it is nontrivial, it selects a uniform nonidentity Pauli
from it, measures that Pauli on two fresh copies, and accepts if the outcomes agree; otherwise it
outputs a fair bit: `4(3h + 2) + 2 = 12h + 10` copies.

**Formalization Note** The family is indexed by `(n, h)`, given to the machine as `1ⁿ 0 1ʰ`. A
Haar-random state is `U|0ⁿ⟩` with `U ∼ μ_H`. `2^{-Ω(n)}` is `2^{-cn}` for one `c > 0` and all large
`n`, uniformly in `h`. -/
theorem lemma_4_4 :
    ∃ D' : (p : ℕ × ℕ) → CopyTest p.1,
      IsUniformFamily (fun p : ℕ × ℕ => List.replicate p.1 true ++ false :: List.replicate p.2 true)
        (fun p => p.1) D' ∧
      (∀ n h : ℕ, (D' (n, h)).K = 12 * h + 10) ∧
      (∀ n h : ℕ, 19 ≤ h → h ≤ n - 2 → ∀ ψ : EuclideanSpace ℂ (Qubits n), IsState ψ →
        n - h ≤ stabDim ψ → (5 / 8 : ℝ) ≤ (D' (n, h)).accept ψ) ∧
      ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ h : ℕ, 19 ≤ h → h ≤ n - 2 →
        ∫ U, (D' (n, h)).accept (act U (zeroKet n)) ∂haarLaw n ≤ 1 / 2 + (2 : ℝ) ^ (-(c * n)) := by sorry

end QuantumHMMR
