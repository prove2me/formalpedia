-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_trivial_and_limits
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.trivial_and_limits
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:04:32.885687+00:00
-- url     : https://prove2.me/theorems/9d06c0ad-0ad4-4567-8645-7249fd0dc96a
-- title:
--   §II.B.3 Eq.(22) and §III.A Eq.(50): trivial cloning and limiting fidelities
-- statement:
--   For $d\ge2$ and $1\le N<M$, appending maximally mixed blanks and incoherently shuffling gives a channel with fidelity $F_{\rm triv}$ strictly below $F_{N\to M}(d)$. Moreover,
--
--   $$
--   F_{\rm triv}=\frac NM+\frac{M-N}{dM},\quad \lim_{d\to\infty}F_{N\to M}(d)=\frac NM,\quad\lim_{M\to\infty}F_{N\to M}(d)=\frac{N+1}{N+d}.
--   $$
--
--   The difference from trivial cloning tends to zero as d tends to infinity. At fixed d and r>1, along any integer sequences N tending to infinity and M=rN, the expansion is F=1−(d−1)(1−1/r)/N+O(N⁻²). No unbounded exact-ratio sequence is asserted to exist for irrational r.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 9, §II.B.3 Eq.(22) and §III.A Eq.(50): trivial cloning and limiting fidelities

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P40

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open MeasureTheory Filter

open scoped Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P12 (sigma)

open QAlgorithms.Papers.Independent.Dependency50.P48 (pureFidelity)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P16
  (CloneMap IsBoseInputChannel coherentTensor tensorWithIdentity canonicalCloner
   HasBoseOutput HasBlackCowCoefficient canonicalCoefficient oneMixed)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector siteObservable)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- II.B.3 PDF p.9 Eqs.(21),(22), III.A PDF p.15 Eq.(50): shuffling baseline and limits.
Fixed-r asymptotics range over genuinely unbounded integer-copy sequences. -/
theorem trivial_and_limits :
    (∀ d N M : ℕ, 2 ≤ d → 1 ≤ N → ∀ hNM : N < M,
      IsBoseInputChannel (shuffleCloner (d := d) hNM.le) ∧
      UniformCloner (shuffleCloner (d := d) hNM.le)
        ((N : ℝ) / M + ((M : ℝ) - N) / (d * M)) ∧
      (N : ℝ) / M + ((M : ℝ) - N) / (d * M) < optimalSingle d N M) ∧
    (∀ N M : ℕ, 1 ≤ N → N < M →
      Tendsto (fun d : ℕ => optimalSingle d N M) atTop (nhds ((N : ℝ) / M)) ∧
      Tendsto (fun d : ℕ => optimalSingle d N M -
        ((N : ℝ) / M + ((M : ℝ) - N) / (d * M))) atTop (nhds 0)) ∧
    (∀ d N : ℕ, 2 ≤ d → 1 ≤ N →
      Tendsto (fun M : ℕ => optimalSingle d N M) atTop (nhds (((N : ℝ) + 1) / (N + d)))) ∧
    (∀ (d : ℕ) (r : ℝ), 2 ≤ d → 1 < r → ∀ n m : ℕ → ℕ,
      Tendsto n atTop atTop → (∀ k, 1 ≤ n k ∧ n k < m k ∧ (m k : ℝ) = r * n k) →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop,
        |optimalSingle d (n k) (m k) -
          (1 - ((d : ℝ) - 1) * (1 - 1 / r) / n k)| ≤ C / (n k : ℝ) ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
