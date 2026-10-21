-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P02_traceClass_norm_factorization_ideal
-- name    : QAlgorithms.Papers.Independent.Next46.P02.traceClass_norm_factorization_ideal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:28:40.192328+00:00
-- url     : https://prove2.me/theorems/1d7bd04d-9ccd-4806-8f6c-707e9b627918
-- title:
--   All trace-class norm, factorization and ideal properties
-- statement:
--   Let $H$ be a complete real or complex Hilbert space, and let $\mathcal B_1(H)$ denote trace class with trace norm $\|T\|_1=\sum_i\langle |T|e_i;e_i\rangle$. All seven assertions hold. The class is linear and this function is a norm. A bounded operator is trace-class exactly when it factors through two Hilbert–Schmidt endomorphisms:
--
--   $$
--   T\in\mathcal B_1(H)\iff \exists A,B\in\mathcal B_2(H),\ T=AB.
--   $$
--
--   Every trace-class $T$ is Hilbert–Schmidt, with $\|T\|_2^2\le\|T\|\|T\|_1$ and $\|T\|_2\le\|T\|_1$. Trace class is a two-sided ideal, and for every bounded $S$,
--
--   $$
--   \max\{\|ST\|_1,\|TS\|_1\}\le\|S\|\,\|T\|_1\quad(T\in\mathcal B_1(H)).
--   $$
--
--   For every bounded $T$, $T^*$ is trace-class if and only if $T$ is; their trace norms agree on this class. Finally every finite-rank bounded operator is trace-class.
--
--   These are properties of the modulus-defined class, with no norm or ideal axiom assumed.
-- source:
--   Trace-Class and Nuclear Operators, arXiv:2204.06954v2, PDF p. 11, §5, Theorem 5.2(a)–(g): trace-class norm, factorization, and ideal

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

/-- PDF pp.11–13, Theorem 5.2(a)–(g): every clause, including all finite-rank
operators and factorization through two Hilbert–Schmidt endomorphisms. -/
theorem traceClass_norm_factorization_ideal :
    NormOn (F := F) (IsModulusTraceClass (F := F) (H := H)) modulusTraceNorm ∧
    (∀ T : H →L[F] H, IsModulusTraceClass T ↔ ∃ A B : H →L[F] H,
      IsHilbertSchmidt A ∧ IsHilbertSchmidt B ∧ T = A.comp B) ∧
    (∀ T : H →L[F] H, IsModulusTraceClass T → IsHilbertSchmidt T ∧
      hilbertSchmidtNorm T ^ 2 ≤ ‖T‖ * modulusTraceNorm T ∧ hilbertSchmidtNorm T ≤ modulusTraceNorm T) ∧
    (∀ S T : H →L[F] H, IsModulusTraceClass T →
      IsModulusTraceClass (S.comp T) ∧ IsModulusTraceClass (T.comp S) ∧
      max (modulusTraceNorm (S.comp T)) (modulusTraceNorm (T.comp S)) ≤ ‖S‖ * modulusTraceNorm T) ∧
    (∀ T : H →L[F] H, (IsModulusTraceClass (ContinuousLinearMap.adjoint T) ↔ IsModulusTraceClass T) ∧
      (IsModulusTraceClass T → modulusTraceNorm T = modulusTraceNorm (ContinuousLinearMap.adjoint T))) ∧
    (∀ T : H →L[F] H, IsFiniteRank T → IsModulusTraceClass T) := by sorry

end Hilbert

end QAlgorithms.Papers.Independent.Next46.P02

end
