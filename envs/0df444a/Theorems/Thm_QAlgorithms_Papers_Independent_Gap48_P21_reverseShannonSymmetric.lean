-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P21_reverseShannonSymmetric
-- name    : QAlgorithms.Papers.Independent.Gap48.P21.reverseShannonSymmetric
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:24:45.402914+00:00
-- url     : https://prove2.me/theorems/5c752ea2-ae82-4c85-9874-7dc91057d67f
-- title:
--   Author note [4]: reverse-Shannon sketch for symmetric channels
-- statement:
--   Let $N$ be a finite memoryless classical channel from one of the source's randomizing or erasure families, up to fixed alphabet bijections, and let $C(N)$ be its Shannon capacity. For every $\varepsilon>0$ there exists a sequence of input-independent random codebooks. At block length $n$, every codebook has at most $2^{b_n}$ output words, where $b_n=\lceil n(C(N)+\varepsilon)\rceil$. The sender samples an output from the native block transition law restricted and renormalized to the chosen book, and transmits its index in $b_n$ bits; a specified member is used if the normalization is zero. Averaging over shared randomness gives a simulated kernel $\widetilde P_n$ satisfying
--
--   $$\lim_{n\to\infty}\max_{u\in X^n}d_{\rm TV}\!\left(\widetilde P_n(\cdot\mid u),N^{\otimes n}(\cdot\mid u)\right)=0.$$
--
--   Here $d_{\rm TV}(p,q)=\frac12\sum_y|p(y)-q(y)|$. Averaging shared randomness before comparison is essential; fixed-book conditional distributions need not approximate the full output law.
-- source:
--   Entanglement-Assisted Classical Capacity of Noisy Quantum Channels, arXiv:quant-ph/9904023v5, PDF p. 4, Author note [4]: reverse-Shannon sketch for symmetric channels

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P21

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.Elementwise

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Gap48.P21

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Reuse the finite Pi-space extended norm explicitly. Matrix has the same
-- product topology, but the generic instance search did not bridge the alias.

attribute [local instance] QAlgorithms.Papers.Independent.Gap48.P21.matrixContinuousENorm

open QAlgorithms.Papers.Independent.Dependency50.P45
  (resourceCapacity standardEbit DMC shannonCapacity blockProb)

open QAlgorithms.Papers.Independent.Claimed50.P43 (finiteWeyl chaotic)

open QAlgorithms.Papers.Independent.Information100.P58 (singleErasure)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

-- CE uses resourceCapacity standardEbit directly; C uses the same accepted
-- operational capacity with the one-dimensional product resource.

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

/-- PDF p.4, note [4]: fixed-budget approximate reverse Shannon for the source
families. Shared randomness is averaged first, error is uniform over inputs,
book mass zero has a physical fallback, and bit budgets are rounded upward. -/
theorem reverseShannonSymmetric {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (N : DMC X Y) (hfamily : SourceClassicalFamily N)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ P : (n : ℕ) → RandomCodebook Y n (Nat.ceil ((n:ℝ)*(shannonCapacity N+eps))),
      Tendsto (fun n => sSup (Set.range fun x : Fin n → X =>
        tvDist (bookAverage N (P n) x) (blockProb N n x))) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P21

end
