-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_observable_function_reversible
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.observable_function_reversible
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:01:38.028034+00:00
-- url     : https://prove2.me/theorems/68c22365-0f08-4512-86bf-1e97cf15debb
-- title:
--   Theorem 2: reversible computation of an observable function
-- statement:
--   Let $\Omega,\Theta$ be finite orthogonal subspace families, let $F:\Omega\to\Theta$, and let a unitary $U$ compute $F$ with error at most $\epsilon\ge0$ on every normalized vector in each input subspace (embedded with initial work zero). Let $T=\sum_W\Pi_W\otimes T_W$ be a measurement operator for $\Theta$, and define $F_T=\sum_V\Pi_V\otimes T_{F(V)}$. Extend $T$ by identity on its support complement and extend $U$ by identity on its extra register. Then, on the full input support tensored with that extra register,
--
--   $$
--   \|(U^{-1}TU-F_T)\xi\|_2\le2\sqrt{|\Omega|\epsilon}\,\|\xi\|_2.
--   $$
--
--   This is a phase-sensitive operator bound uniform over all coherent label combinations and entangled extra-register states. Neither family need be complete and $F$ need not be injective.
--
--   It quantifies the approximate cleanup achieved by compute, control and uncompute.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 20, Theorem 2: reversible computation of an observable function

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF pp.20–21, Theorem 2: compute, apply a measurement-controlled operator, uncompute.
Omega is already embedded in the full computer memory with clean initial work; the bound
holds on its entire support tensor D, including entangled states and coherent label mixtures.
No completeness or injectivity of the observable function is assumed. -/
theorem observable_function_reversible {I : Type*} [Fintype I] [DecidableEq I]
    (r s d : ℕ) (O : OrthogonalProjectorFamily I r) (Theta : OrthogonalProjectorFamily I s) (F : Fin r → Fin s)
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (V : Fin s → Matrix (Qubits d) (Qubits d) ℂ)
    (hV : ∀ v, V v ∈ Matrix.unitaryGroup (Qubits d) ℂ)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hcomputes : ∀ (v : Fin r) (x : EuclideanSpace ℂ I), IsState x → act (O.proj v) x = x →
      1 - epsilon ≤ subspaceProbability (pureDensity (act U x)) (Theta.proj (F v))) :
    ∀ x : EuclideanSpace ℂ (I × Qubits d),
      act (O.support ⊗ₖ (1 : Matrix (Qubits d) (Qubits d) ℂ)) x = x →
      ‖act ((Uᴴ ⊗ₖ (1 : Matrix (Qubits d) (Qubits d) ℂ)) * measurementMatrix Theta V *
          (U ⊗ₖ (1 : Matrix (Qubits d) (Qubits d) ℂ))) x -
        act (measurementMatrix O (fun v => V (F v))) x‖ ≤
        2 * Real.sqrt ((r : ℝ) * epsilon) * ‖x‖ := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
