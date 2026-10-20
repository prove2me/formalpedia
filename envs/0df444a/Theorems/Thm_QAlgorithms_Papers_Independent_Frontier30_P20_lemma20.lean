-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_lemma20
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.lemma20
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:49:24.97498+00:00
-- url     : https://prove2.me/theorems/6e52b588-82fb-4e86-a787-8796d77d63e6
-- title:
--   Lemma 20 (rank-two qubit normal representation)
-- statement:
--   Let $T$ be a CPTP map on $M_2(\mathbb C)$, a qubit channel. Composition applies the rightmost factor first; map norms are induced Hilbert–Schmidt norms. If $T$ has Kraus rank exactly two, there exist unitary conjugations $U,V$, vectors $a,b\in\mathbb C^2$, and a real number $x$, with real zeroth components $a_0,b_0$, such that
--
--   $$T=UCV,\quad C(\rho)=A_1\rho A_1^\dagger+A_2\rho A_2^\dagger,$$
--
--   where $A_1=|0\rangle\langle a|$, $A_2=|0\rangle\langle b|+x|1\rangle\langle1|$, and $|a\rangle\langle a|+|b\rangle\langle b|=I-x^2|1\rangle\langle1|$.
--
--   This supplies the constructed normal representation used in the rank-two analysis.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 18, Lemma 20 (rank-two qubit normal representation)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Lemma 20, PDF pp.17--18: the Kraus vectors and x are existential data, not a prescribed factorization. -/
theorem lemma20 (T : Super 2) (hT : Channel T) (hrank : krausRank T = 2) :
    ∃ (U V : Super 2) (a b : Fin 2 → ℂ) (x : ℝ),
      IsUnitaryConjugation U ∧ IsUnitaryConjugation V ∧ CanonicalData a b x ∧
      T = U * canonicalChannel a b x * V := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
