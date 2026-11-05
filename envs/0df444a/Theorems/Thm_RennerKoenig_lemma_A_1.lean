-- Prove2me | Theorems.Thm_RennerKoenig_lemma_A_1
-- name    : RennerKoenig.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:46:17.404546+00:00
-- url     : https://prove2.me/theorems/a4d67469-3965-4f52-9db3-48b82dc99b5e
-- title:
--   Lemma A.1 — Schur's inequality, with its equality clause
-- statement:
--   Let $A$ be a linear operator on a $d$-dimensional Hilbert space and let $\lambda_1,\dots,\lambda_d$ be its eigenvalues. Then
--
--   $$
--   \sum_{i=1}^d|\lambda_i|^2\le\operatorname{tr}(AA^\dagger),
--   $$
--
--   with equality if and only if $A$ is normal, that is, $AA^\dagger=A^\dagger A$.
--
--   The normal case gives the identity behind Lemma A.2.
--
--   Differences from the source:
--   - encoding: the eigenvalues λ₁, …, λ_d of a linear operator → the multiset of roots of the characteristic polynomial, for a bounded operator on a finite-dimensional space; reason: d eigenvalues means algebraic multiplicity, and every linear map on a finite-dimensional space is bounded
--   - encoding: tr → series over a chosen Hilbert basis; real part where the page treats the trace as a real number; reason: the trace of a trace-class operator is independent of the basis and is real on the self-adjoint operators involved
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, Lemma A.1, p.12

import Mathlib
import Definitions.Def_RennerKoenig_tr

namespace RennerKoenig

/-- **Lemma A.1 (Schur's inequality).** Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, Lemma A.1, p.12: for a linear operator `A` on a
`d`-dimensional Hilbert space with eigenvalues `λ₁, …, λ_d`, `∑ᵢ |λᵢ|² ≤ tr(AA†)`, with equality if
and only if `A` is normal.

**Formalization Note** The eigenvalues are the multiset of roots of the characteristic polynomial,
`d` of them, counted with algebraic multiplicity. -/
theorem lemma_A_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
    (A : H →L[ℂ] H) :
    ((A : H →ₗ[ℂ] H).charpoly.roots.map (fun l => ‖l‖ ^ 2)).sum ≤ (tr (A * ContinuousLinearMap.adjoint A)).re ∧ (((A : H →ₗ[ℂ] H).charpoly.roots.map (fun l => ‖l‖ ^ 2)).sum = (tr (A * ContinuousLinearMap.adjoint A)).re ↔ A * ContinuousLinearMap.adjoint A = ContinuousLinearMap.adjoint A * A) := by sorry

end RennerKoenig
