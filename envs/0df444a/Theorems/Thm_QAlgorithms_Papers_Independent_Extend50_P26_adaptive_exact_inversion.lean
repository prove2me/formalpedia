-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P26_adaptive_exact_inversion
-- name    : QAlgorithms.Papers.Independent.Extend50.P26.adaptive_exact_inversion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:27:25.364747+00:00
-- url     : https://prove2.me/theorems/27c31a8c-bc60-4000-9460-2b9d9dea3642
-- title:
--   Exact adaptive inversion with exponential failure decay
-- statement:
--   Let $d\ge2$ and $k\ge0$ be integers. A single fixed adaptive heralded protocol, depending only on $d$ and $k$, uses at most $k$ forward applications of an unknown $U\in SU(d)$ and implements the inverse channel exactly on success. Its success probability, independent of $U$ and the input, is
--
--   $$p_S=1-\left(1-\frac1{d^2}\right)^{\lfloor(k+1)/d\rfloor}.$$
--
--   More precisely, its success branch is the completely positive map $\rho\mapsto p_S U^\dagger\rho U$, also when the input is entangled with a reference. Finite ancillas, fixed channels, measurements, and classical feed-forward are free. Oracle calls are the only uses counted; unused slots may be discarded. For $k<d-1$ the success branch is zero. Scalar phases do not change the physical channel, so the result covers every unitary operation.
--
--   This is an achieving protocol and makes no claim of global optimality.
-- source:
--   Reversing Unknown Quantum Transformations: Universal Quantum Circuit for Inverting General Unitary Operations, arXiv:1810.06944v3, PDF p. 3, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P26

noncomputable section

open QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P26

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.3, Theorem 1 (paper headline on p.1): an achieving universal adaptive
protocol; no optimality assertion. At k<d-1 the heralded branch has probability zero. -/
theorem adaptive_exact_inversion (d k : ℕ) (hd : 2 ≤ d) :
    Attainable .adaptive d k (adaptiveInversionProbability d k) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P26

end
