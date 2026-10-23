-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P27_decohered_and_random_fidelities
-- name    : QAlgorithms.Papers.Independent.Claimed50.P27.decohered_and_random_fidelities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:21:20.479115+00:00
-- url     : https://prove2.me/theorems/fc9a7451-bc9b-4ca1-99fb-b772f10165da
-- title:
--   Decohered-memory and independent-random-gate fidelities
-- statement:
--   Let $d\ge2$ and dephase only the two-dimensional memory in the $+,-$ basis after the preprocessing $A$ and before the postprocessing $B$ of Theorem 1. With $P_i$ the symmetric/antisymmetric projectors and $d_i$ their dimensions, the resulting one-call channel is
--
--   $$C_U^{\mathrm{deco}}(\rho)=\sum_{i=\pm}\frac d{d_i}P_i[U\operatorname{Tr}_E(P_i\rho P_i)U^\dagger\otimes I]P_i.$$
--
--   For a second comparator, apply $U$ to the first external register and an independently probability-Haar-random unitary to the second. Their average global channel fidelities, normalized exactly as in Eq. (4), satisfy
--
--   $$F_{\mathrm{deco}}=\frac1{d^2},\qquad F_{\mathrm{ran}}=\frac1{d^2}.$$
--
--   These are two different circuits with the same score. The statement includes the exact decohered-channel formula and makes no equality claim about the two output channel families.
-- source:
--   Optimal cloning of unitary transformations, arXiv:0804.0129v2, PDF p. 3, Final paragraph, p.3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P27

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.3: both comparison circuits have fidelity 1/d^2.
Equal scores do not assert equality of their output channels. -/
theorem decohered_and_random_fidelities (d : ℕ) (hd : 2 ≤ d) :
    (∀ U : (Matrix.unitaryGroup (Fin d) ℂ), decoheredFamily d U = decoheredFormula d U) ∧
    familyScore (decoheredFamily d) = 1 / (d : ℝ)^2 ∧
    familyScore (randomFamily d) = 1 / (d : ℝ)^2 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P27

end
