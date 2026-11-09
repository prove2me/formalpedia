-- Prove2me | Theorems.Thm_SharpJL_Dimension_proposition_3_1
-- name    : SharpJL.Dimension.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:09:37.539383+00:00
-- url     : https://prove2.me/theorems/3f0d78e7-e9d6-46b7-8ede-ed84036643c0
-- title:
--   Proposition 3.1 — symmetric contraction with many boundary eigenvalues
-- statement:
--   There is a universal constant $C_1>0$ such that, for every pair of integers $k,m\ge1$ and every indexed family of Euclidean unit vectors $w_1,\ldots,w_m\in\mathbb R^k$, there is a real symmetric matrix $Q$ with
--
--   $$
--   -I\preceq Q\preceq I,\qquad
--   \#\{i:\lambda_i(Q)\in\{-1,1\}\}\ge\lceil k/4\rceil,
--   \qquad
--   \max_{1\le\ell\le m}|w_\ell^{\mathsf T}Qw_\ell|
--   \le C_1\sqrt{\frac{\log(3+m/k^2)}{k}}.
--   $$
--
--   Here $\preceq$ is positive semidefinite order, $\lambda_i(Q)$ lists eigenvalues with multiplicity, and $\log$ is the natural logarithm. Repetitions among the unit vectors are allowed. This supplies simultaneous quadratic-form control together with exact spectral saturation, the supporting statement for rank reduction.
--
--   Differences from the source:
--   - encoding: m indexed unit vectors in ℝ^k → Fin m indexed families in EuclideanSpace ℝ (Fin k); reason: zero-based coordinates and indices change no instances and allow repeated vectors
--   - encoding: a maximum over the m prescribed quadratic-form errors → the displayed error bound holds for every index in Fin m; reason: m ≥ 1 makes the pointwise bound equivalent to the finite maximum bound
--   - encoding: Q symmetric with −I ⪯ Q ⪯ I → SpencerEight.IsSymmContraction Q; reason: for real symmetric matrices the L2 operator norm is the largest absolute eigenvalue, so the published predicate is equivalent to both Loewner inequalities
--   - encoding: at least ⌈k/4⌉ eigenvalues equal to 1 or −1, counted with multiplicity → the sum of the real dimensions of ker(I−Q) and ker(I+Q) is at least Nat.ceil ((k : ℝ) / 4); reason: real symmetric matrices are diagonalizable and the two eigenspaces are disjoint, so their dimensions count exactly the required multiplicities
-- source:
--   Vishesh Jain, STOC 2027 submission #707 (October 2026), The Sharp Dimension Bound in the Johnson--Lindenstrauss Lemma, Proposition 3.1, p.9 (PDF p.9); §1.4 conventions p.6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/707.pdf#page=9

import Mathlib
import Definitions.Def_SpencerEight_IsSymmContraction

namespace SharpJL.Dimension

/-- Jain, STOC 2027 submission #707 (October 2026), Proposition 3.1, p.9.
The two kernel dimensions count the eigenvalues +1 and -1 with multiplicity.
For a real symmetric matrix the referenced L2 contraction predicate is
equivalent to the source's Loewner inequalities `-I ⪯ Q ⪯ I`. -/
theorem proposition_3_1 :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ (k m : ℕ), 1 ≤ k → 1 ≤ m →
      ∀ (w : Fin m → EuclideanSpace ℝ (Fin k)),
        (∀ ℓ, ‖w ℓ‖ = 1) →
        ∃ Q : Matrix (Fin k) (Fin k) ℝ,
          SpencerEight.IsSymmContraction Q ∧
          ⌈(k : ℝ) / 4⌉₊ ≤
            Module.finrank ℝ (LinearMap.ker (1 - Q).mulVecLin) +
            Module.finrank ℝ (LinearMap.ker (1 + Q).mulVecLin) ∧
          ∀ ℓ : Fin m,
            |∑ i : Fin k, ∑ j : Fin k, w ℓ i * Q i j * w ℓ j| ≤
              C₁ * Real.sqrt (Real.log (3 + (m : ℝ) / (k : ℝ) ^ 2) / (k : ℝ)) := by sorry

end SharpJL.Dimension
