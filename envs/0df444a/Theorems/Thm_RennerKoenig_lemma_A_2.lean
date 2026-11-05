-- Prove2me | Theorems.Thm_RennerKoenig_lemma_A_2
-- name    : RennerKoenig.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:46:41.05332+00:00
-- url     : https://prove2.me/theorems/9d8d4882-2982-4798-af8a-9a663a17a8ec
-- title:
--   Lemma A.2 — $\operatorname{tr}|A|\le\sqrt r\sqrt{\operatorname{tr}(AA^\dagger)}$ for normal $A$ of rank $r$
-- statement:
--   Let $A$ be a normal operator of rank $r$ on a Hilbert space. Then
--
--   $$
--   \operatorname{tr}|A|\le\sqrt r\,\sqrt{\operatorname{tr}(AA^\dagger)}.
--   $$
--
--   This is the operator form of the bound of an $\ell^1$ norm by an $\ell^2$ norm on a set of known size, and it is where the rank enters the final bound.
--
--   Differences from the source:
--   - encoding: rank r, possibly infinite → hypothesis that the range of A is finite-dimensional; reason: the page takes r nonzero eigenvalues, so r is finite
--   - encoding: tr|·| → published nuclear norm traceNormValue; reason: equal on trace-class operators, and only differences of density operators are measured
--   - encoding: tr → series over a chosen Hilbert basis; real part where the page treats the trace as a real number; reason: the trace of a trace-class operator is independent of the basis and is real on the self-adjoint operators involved
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, Lemma A.2, p.13

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_RennerKoenig_tr
import Definitions.Def_RennerKoenig_rankOp

open QAlgorithms.Papers.Independent.Dependency50.P13

namespace RennerKoenig

/-- **Lemma A.2.** Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, Lemma A.2, p.13: for a normal operator `A` of rank `r`,
`tr|A| ≤ √r √(tr(AA†))`.

**Formalization Note** The hypothesis `hfin` says that `r` is finite; for infinite rank and
`A ≠ 0` the right side is `+∞` or the left side undefined. -/
theorem lemma_A_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H)
    (hA : A * ContinuousLinearMap.adjoint A = ContinuousLinearMap.adjoint A * A)
    (hfin : FiniteDimensional ℂ (LinearMap.range
    (A : H →ₗ[ℂ] H))) :
    traceNormValue A ≤ Real.sqrt (rankOp A) * Real.sqrt (tr (A * ContinuousLinearMap.adjoint A)).re := by sorry

end RennerKoenig
