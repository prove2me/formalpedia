-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P34_incoherent_traceAnnihilators
-- name    : QAlgorithms.Papers.Independent.Information100.P34.incoherent_traceAnnihilators
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:59:14.227587+00:00
-- url     : https://prove2.me/theorems/88275fa1-e446-49d4-b50b-03f889a4b86a
-- title:
--   Lemma 27: explicit trace-annihilator spaces of incoherent affine channel sets
-- statement:
--   Let $A,B$ be arbitrary finite systems of positive dimensions $a,b$. For Hermitian $X$ on $A\otimes B$, define $\operatorname{aff}(O)^*=\{X:\operatorname{Tr}(XJ_M)=0\text{ for every }M\in O(A\to B)\}$. Then
--
--   $$X\in\operatorname{aff}(\mathrm{MIO})^*\iff X=P\otimes I_B+\sum_i|i\rangle\langle i|\otimes Q_i,\quad\operatorname{Tr}P=0,\quad\Delta Q_i=0,$$
--   $$X\in\operatorname{aff}(\mathrm{DI})^*\iff X=P\otimes I_B+\sum_iQ_i\otimes|i\rangle\langle i|,\quad\operatorname{Tr}P=0,\quad\Delta Q_i=0,$$
--   $$X\in\operatorname{aff}(\mathrm{DIO})^*\iff X=P\otimes I_B+(\Delta_A-\Delta_B)Q,\quad\operatorname{Tr}P=0.$$
--
--   All witnesses $P,Q_i,Q$ are Hermitian; none is required to be positive. The partial dephasings act on their indicated factors. These are trace-annihilator spaces, distinct from positive dual cones.
-- source:
--   The Structure of Higher-Order Quantum Resources with an Application to Coherence, arXiv:2609.40186v1, PDF p. 55, Lemma 27

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P34

/-- Lemma 27, Eqs.(C252a-c), PDF pp.55-57. Each equivalence ranges over
Hermitian X; all P and Q witnesses are constructed existentially. -/
theorem incoherent_traceAnnihilators {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.IsHermitian) :
    (TraceAnnihilator .mio X ↔
      ∃ P : Matrix (Fin a) (Fin a) ℂ, ∃ Q : Fin a → Matrix (Fin b) (Fin b) ℂ,
        P.IsHermitian ∧ P.trace = 0 ∧
        (∀ i, (Q i).IsHermitian ∧ dephasing (Q i) = 0) ∧
        X = Matrix.kronecker P 1 +
          ∑ i, Matrix.kronecker (Matrix.single i i 1) (Q i)) ∧
    (TraceAnnihilator .di X ↔
      ∃ P : Matrix (Fin a) (Fin a) ℂ, ∃ Q : Fin b → Matrix (Fin a) (Fin a) ℂ,
        P.IsHermitian ∧ P.trace = 0 ∧
        (∀ i, (Q i).IsHermitian ∧ dephasing (Q i) = 0) ∧
        X = Matrix.kronecker P 1 +
          ∑ i, Matrix.kronecker (Q i) (Matrix.single i i 1)) ∧
    (TraceAnnihilator .dio X ↔
      ∃ P : Matrix (Fin a) (Fin a) ℂ,
      ∃ Q : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
        P.IsHermitian ∧ P.trace = 0 ∧ Q.IsHermitian ∧
        X = Matrix.kronecker P 1 + (dephaseInput Q - dephaseOutput Q)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P34

end
