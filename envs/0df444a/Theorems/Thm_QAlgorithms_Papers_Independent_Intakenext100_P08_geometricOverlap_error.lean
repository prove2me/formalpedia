-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P08_geometricOverlap_error
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P08.geometricOverlap_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:00:39.544298+00:00
-- url     : https://prove2.me/theorems/a128f3ad-eed9-4b74-aee9-ca5e1108215a
-- title:
--   Unconditional geometric overlap decoding bound
-- statement:
--   Fix $N\ge1$, coordinate noise variance $v>0$, radius $a>0$, and cell volume $\Delta>0$. There is a real symplectic matrix $S$ such that the row lattice $\Lambda=L(\Delta^{1/(2N)}S)$ has covolume $\Delta$ and, for a random vector $\xi\in\mathbb R^{2N}$ with independent $N(0,v)$ coordinates,
--
--   $$
--   \Pr\{\xi\notin\operatorname{Vor}_0(\Lambda)\}\le\Pr\{\|\xi\|>a\}+\frac{V_{2N}a^{2N}}{\Delta}.
--   $$
--
--   The lattice is chosen before the displacement is sampled. The central Voronoi cell uses the Euclidean norm; boundaries have zero Gaussian measure. The first term restores the atypical shifts expressly omitted in (59)–(64). This bounds a geometric decoding event and does not establish quantum-code fidelity.
-- source:
--   Achievable rates for the Gaussian quantum channel, arXiv:quant-ph/0105058v1, PDF p. 6, §V, (58)–(64): overlap decoding bound with the omitted tail restored

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P08

namespace QAlgorithms.Papers.Independent.Intakenext100.P08

open MeasureTheory ProbabilityTheory Matrix

open scoped BigOperators ENNReal

-- Accepted grouped index and source-sign matrix; no paper-local copies.

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)
-- The accepted predicate uses column bases and -sigma: apply it to S.transpose.

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)
-- The accepted pairing has the opposite sign: exchange its two arguments below.

open QAlgorithms.Papers.Independent.Frontier30.P10 (symplecticPair)

/-- PDF pp.6–7, (58)–(64): unconditional geometric overlap bound.
Printed/changed/why: (61) explicitly ignores shifts larger than a; add their
Gaussian tail to bound the full failure probability. This is not physical-code achievability. -/
theorem geometricOverlap_error (N : ℕ) (hN : 1 ≤ N) (v : NNReal) (hv : 0 < v)
    (a Delta : ℝ) (ha : 0 < a) (hDelta : 0 < Delta) :
    ∃ S : Generator N, IsSymplectic S.transpose ∧ S.det ≠ 0 ∧
      let M : Generator N := Delta ^ (1 / (2 * (N : ℝ))) • S
      |M.det| = Delta ∧
      decodingFailure M v ≤ displacementTail N v a +
        unitBallVolume (2 * N) * a ^ (2 * N) / Delta := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P08
