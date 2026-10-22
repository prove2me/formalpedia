-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaB_10
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemmaB_10
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:55:16.635474+00:00
-- url     : https://prove2.me/theorems/13b484c3-f847-4d84-9b46-1a02f6a61bbb
-- title:
--   Symmetric purification with a sufficient ancilla
-- statement:
--   Let $D,R$ be nonzero finite-dimensional systems with $\dim R\ge\dim D$, and let $\rho$ be a nonnegative operator on $D^{\otimes n}$ invariant under copy permutations. Then there is a vector $\psi$ on $D^{\otimes n}\otimes R^{\otimes n}$ such that
--
--   $$\operatorname{tr}_{R^{\otimes n}}|\psi\rangle\langle\psi|=\rho,\qquad (P_\pi\otimes P_\pi)\psi=\psi\quad\text{for every }\pi\in S_n.$$
--
--   The positivity assumption is supplied by Appendix B's stated nonnegative-operator setting; its omission from the lemma's printed sentence is recorded in SOURCE_CORRECTIONS.md. The dimension condition is retained, and zero input admits the zero purification.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 23, Lemma B.10

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Lemma B.10 (PDF p.23): the surrounding appendix supplies the implicit
nonnegativity of rho, omitted in the printed sentence. The ancilla dimension
bound is retained. Permutation invariance of the purification is explicit. -/
theorem lemmaB_10 {D R : Type*} [Fintype D] [Fintype R]
    [DecidableEq D] [DecidableEq R] [Nonempty D] [Nonempty R]
    (n : ℕ) (rho : Op (Fin n → D)) (hrho : rho.PosSemidef)
    (hinv : copyPermutationInvariant rho) (hdim : Fintype.card D ≤ Fintype.card R) :
    ∃ psi : ((Fin n → D) × (Fin n → R)) → ℂ,
      UnnormalizedPurifies psi rho ∧ ∀ (p : Equiv.Perm (Fin n)) x,
        psi (x.1 ∘ p, x.2 ∘ p) = psi x := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
