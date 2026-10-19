-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P18_isometricEquivalence_reversible
-- name    : QAlgorithms.Papers.Independent.Frontier18.P18.isometricEquivalence_reversible
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:07:24.455979+00:00
-- url     : https://prove2.me/theorems/12c0faa1-0876-4c72-8ac4-6d01b3be9ad1
-- title:
--   Lemma 1: isometric equivalence preserves reversibility
-- statement:
--   Let $\Phi:\mathfrak T(\mathcal H_A)\to\mathfrak T(\mathcal H_B)$ and $\Phi':\mathfrak T(\mathcal H_A)\to\mathfrak T(\mathcal H_{B'})$ be quantum channels on nonzero finite dimensional or separable complex Hilbert spaces. Suppose a partial isometry $W:\mathcal H_B\to\mathcal H_{B'}$ satisfies $\Phi'(X)=W\Phi(X)W^*$ and $\Phi(X)=W^*\Phi'(X)W$ for every trace-class $X$. For any set $S$ of normalized input states,
--
--   $$
--   \Phi\text{ is reversible on }S\quad\Longleftrightarrow\quad\Phi'\text{ is reversible on }S.
--   $$
--
--   Reversibility means existence of one completely positive trace-preserving recovery map that recovers every state in $S$. The set $S$ may be empty, uncountable, or non-total. The result permits a change of output support without changing reversibility.
-- source:
--   Monotonicity of the Holevo quantity: a necessary condition for equality in terms of a channel and its applications, arXiv:1106.3297v6, PDF p. 9, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18

noncomputable section

open Filter

open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

-- Use the complex unital C-star calculus directly on bounded operators.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Frontier18.P18

open QAlgorithms.RealRegisters (Hilbert)

/-- Lemma 1, PDF p.9 (isometric equivalence is (3), pp.3–4).
Reversibility is invariant under the partial-isometry equivalence of channels.
Nonempty bases express the standing convention of nonzero physical Hilbert spaces;
S itself may be empty. -/
theorem isometricEquivalence_reversible
    {I J K : Type} [Countable I] [Countable J] [Countable K]
    [Nonempty I] [Nonempty J] [Nonempty K]
    (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (PhiPrime : Matrix I I ℂ → Matrix K K ℂ)
    (hPhi : QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClassChannel Phi)
    (hPhiPrime : QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClassChannel PhiPrime)
    (hEquiv : IsometricallyEquivalent Phi PhiPrime) (S : Set (QAlgorithms.Papers.Independent.Dependency50.P33.State I)) :
    ReversibleOn Phi S ↔ ReversibleOn PhiPrime S := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P18

end
