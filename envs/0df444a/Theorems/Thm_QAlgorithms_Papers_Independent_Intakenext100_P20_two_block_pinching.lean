-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P20_two_block_pinching
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P20.two_block_pinching
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:42:21.91795+00:00
-- url     : https://prove2.me/theorems/1c11d65e-d78f-491a-a9ab-b28efaccdee0
-- title:
--   Appendix D, (D1): two-block pinching
-- statement:
--   Let $\rho$ be a positive semidefinite trace-one operator on a nonzero finite-dimensional complex Hilbert space. For every orthogonal projection $P=P^\dagger=P^2$,
--
--   $$P\rho P+(I-P)\rho(I-P)\succeq\tfrac12\rho.$$
--
--   The order is the positive semidefinite operator order. This two-block pinching inequality is the operator comparison used in the positive-decoder converse.
-- source:
--   Exponents of quantum fixed-length pure state source coding, arXiv:quant-ph/0202002v6, PDF p. 11, Appendix D, (D1): two-block pinching

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P20

noncomputable section

open scoped Matrix ENNReal ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P20

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P47 (IsProbability)

open QAlgorithms.Papers.Independent.Information100.P53 (SpectralData)

open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)

open QAlgorithms.Papers.Independent.Dependency50.P28 (classicalD)

attribute [local instance] Classical.propDecidable

/-- Appendix D, PDF p.11, (D1): two-block pinching dominates half the state.
Projection means self-adjoint and idempotent, and rho remains normalized. -/
theorem two_block_pinching {d : ℕ} (hd : 0 < d)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (P : Matrix (Fin d) (Fin d) ℂ) (hself : Pᴴ = P) (hidempotent : P * P = P) :
    (P * rho * P + (1 - P) * rho * (1 - P) - (1 / 2 : ℂ) • rho).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P20

end
