-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_reversible_completeness
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.reversible_completeness
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:52:10.098184+00:00
-- url     : https://prove2.me/theorems/b1ceef92-188a-4486-8931-e4dcb59a41df
-- title:
--   §2.2 Corollaries, item 2 and the R basis
-- statement:
--   Let $N,M\subseteq\{0,1\}^n$, and let $G:N\to M$ be a bijection. Each of the bases $C_\tau$ and $R=\{\mathrm{NOT},\mathrm{CNOT},\mathrm{Toffoli}\}$ admits an exact finite operation sequence satisfying
--
--   $$
--   |x,0\rangle\longmapsto |G(x),0\rangle\qquad(x\in N).
--   $$
--
--   Here $C_\tau$ consists of the XOR lifts of NOT and AND together with CNOT. There is no efficiency claim for an arbitrary bijection.
--
--   This supplies the source's clean reversible completeness in both stated bases.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 8, §2.2 Corollaries, item 2 and the R basis

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.8, Corollary 2 and the next paragraph: exact clean representation of every
partial bijection in both C_tau and R. No efficiency bound is claimed. -/
theorem reversible_completeness (n : ℕ) (N M : Set (Qubits n)) (e : N ≃ M) :
    (∃ (w : ℕ) (c : Circuit cTauBasis (n + w)), ∀ x : N,
      act c.unitary (inputState x.val w) = inputState (e x).val w) ∧
    (∃ (w : ℕ) (c : Circuit rBasis (n + w)), ∀ x : N,
      act c.unitary (inputState x.val w) = inputState (e x).val w) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
