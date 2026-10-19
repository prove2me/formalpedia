-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P14_singletBellViolation
-- name    : QAlgorithms.Papers.Independent.Frontier18.P14.singletBellViolation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:09:25.883797+00:00
-- url     : https://prove2.me/theorems/d64f096c-83fb-4abe-9bf1-eda12abd3760
-- title:
--   Singlet correlations and maximal CHSH violation
-- statement:
--   Let $|\psi\rangle=(|+,-\rangle-|-,+\rangle)/\sqrt2$ in two polarization qubits, with the Pauli convention (4.5). The state is normalized. For any unit real directions $a,b\in\mathbb R^3$,
--
--   $$D(a,b)=\langle\psi|(a\cdot\sigma)\otimes(b\cdot\sigma)|\psi\rangle=-a\cdot b.$$
--
--   For all four unit directions $a,a',b,b'$, the CHSH expression $D(a,b)+D(a,b')+D(a',b)-D(a',b')$ has absolute value at most $2\sqrt2$, and some four unit directions attain $2\sqrt2$. Hence the singlet attains the stated maximal factor $\sqrt2$ violation of the classical bound $2$. This targets the explicit singlet computation rather than the cited hidden-variable theorem.
-- source:
--   Quantum Physics of Simple Optical Instruments, arXiv:quant-ph/0305007v2, PDF p. 33, §6.3: singlet correlations and maximal CHSH violation

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Dependency50.P34 (fockKet)

/-- PDF pp.32–33, (6.17)–(6.20): actual normalized singlet
correlations, upper bound 2 sqrt(2) on CHSH for all unit polarizer directions,
and attainment of that bound. This states the maximal violation, not the general
hidden-variable Bell inequality cited by the paper. -/
theorem singletBellViolation :
    (∑ ij : Fin 2 × Fin 2, Complex.normSq (singlet ij)) = 1 ∧
    (∀ a b : Fin 3 → ℝ, unitDirection a → unitDirection b →
      singletCorrelation a b = -(∑ i, a i * b i)) ∧
    (∀ a ap b bp : Fin 3 → ℝ,
      unitDirection a → unitDirection ap → unitDirection b → unitDirection bp →
      |chsh a ap b bp| ≤ 2 * Real.sqrt 2) ∧
    (∃ a ap b bp : Fin 3 → ℝ,
      unitDirection a ∧ unitDirection ap ∧ unitDirection b ∧ unitDirection bp ∧
      chsh a ap b bp = 2 * Real.sqrt 2) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P14

end
