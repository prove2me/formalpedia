-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P57_exact_network_extensions
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P57.exact_network_extensions
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:16:04.627204+00:00
-- url     : https://prove2.me/theorems/4288bb53-702d-4bf9-8ce9-0724a262269c
-- title:
--   Extensions: exact local expectations from a product-observable evaluator
-- statement:
--   Fix $s\ge0$. Suppose a normalized base vector $\psi$ has an exact evaluator for $\langle\psi,(\bigotimes_k F_k)\psi\rangle$, uniformly for arbitrary complex $2\times2$ local matrices $F_k$, including non-Hermitian factors. For every observable $O$ supported on at most $s$ sites, one graph enhancement followed by local unitaries admits an exact scalar reduction with
--
--   $$\#\text{base calls}\le4^s,\qquad \mathrm{work}\le C_s(N+1)^3+4^sB,$$
--
--   when each base evaluation costs at most $B$ operations uniformly in the factors. Alternatively, for a supplied unitary Clifford circuit of length $\ell$, followed by local unitaries, there is a separate reduction with
--
--   $$\#\text{base calls}\le4^s,\qquad \mathrm{work}\le C_s(N+\ell+1)^3+4^sB.$$
--
--   The programs precede all numerical data; their calls, factor formation, and scalar output evaluation have explicit semantics. Thus an efficient exact base evaluator yields efficient fixed-support expectations under either enhancement. Clifford conjugation may spread support. These reductions do not assert arbitrary alternation of the two enhancement layers.
-- source:
--   Renormalization algorithm with graph enhancement, arXiv:0802.1211v1, PDF p. 4, Extensions: exact local expectations from a product-observable evaluator

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P57

noncomputable section

open scoped ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Intakethird100.P57

attribute [local instance] Classical.propDecidable

/-- PDF p.4 Extensions: exact conditional reductions, separately for one graph layer or
one Clifford circuit. For support ≤s, at most 4^s arbitrary product evaluations are used;
all other scalar work is polynomial in N and circuit length. Each product call is charged
B in addition to explicit factor formation. Thus any efficient exact base evaluator gives
an efficient local evaluator. No approximate-evaluation contract or alternating enhancement
layers are asserted, and Clifford propagation need not preserve small support. -/
theorem exact_network_extensions :
    ∀ s : ℕ, ∃ C : ℕ, 0 < C ∧
      ∃ (graphPrograms : (N : ℕ) → (S : Finset (Fin N)) → EnhancementProgram N S)
        (cliffordPrograms : (N : ℕ) → (S : Finset (Fin N)) →
          List (QubitCliffordGate N) → EnhancementProgram N S),
      ∀ (N : ℕ) (S : Finset (Fin N)), 1 ≤ N → S.card ≤ s →
        let gp := graphPrograms N S
        (gp.scalar.calls ≤ 4 ^ s ∧
          (∀ B : ℕ, gp.scalar.work B ≤ C * (N + 1) ^ 3 + 4 ^ s * B) ∧
          (∀ (psi : EuclideanSpace ℂ (Qubits N)) (hpsi : IsState psi)
            (base : (Fin N → Matrix Bool Bool ℂ) → ℂ), ExactProductEvaluator psi base →
            ∀ (G : PhaseGraph N) (V : Fin N → Matrix.unitaryGroup Bool ℂ)
              (O : Matrix (S → Bool) (S → Bool) ℂ),
              ∃ mem : ℕ → ℂ,
                gp.scalar.execute (enhancementData G V O) base = some mem ∧
                gp.output < gp.scalar.code.length ∧
                mem gp.output = inner ℂ (enhance G V psi)
                  (act (supportedOp S O) (enhance G V psi)))) ∧
        (∀ circuit : List (QubitCliffordGate N),
          let cp := cliffordPrograms N S circuit
          cp.scalar.calls ≤ 4 ^ s ∧
          (∀ B : ℕ, cp.scalar.work B ≤ C * (N + circuit.length + 1) ^ 3 + 4 ^ s * B) ∧
          (∀ (psi : EuclideanSpace ℂ (Qubits N)) (hpsi : IsState psi)
            (base : (Fin N → Matrix Bool Bool ℂ) → ℂ), ExactProductEvaluator psi base →
            ∀ (G : PhaseGraph N) (V : Fin N → Matrix.unitaryGroup Bool ℂ)
              (O : Matrix (S → Bool) (S → Bool) ℂ),
              let chi := act (productOp fun k => (V k : Matrix Bool Bool ℂ))
                (act (cliffordMatrix circuit) psi)
              ∃ mem : ℕ → ℂ,
                cp.scalar.execute (enhancementData G V O) base = some mem ∧
                cp.output < cp.scalar.code.length ∧
                mem cp.output = inner ℂ chi (act (supportedOp S O) chi))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P57

end
