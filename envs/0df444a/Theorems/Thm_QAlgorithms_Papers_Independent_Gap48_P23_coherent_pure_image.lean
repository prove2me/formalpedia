-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_coherent_pure_image
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.coherent_pure_image
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:57:05.537995+00:00
-- url     : https://prove2.me/theorems/39e208c0-dd85-4b81-8799-b3a194a64c13
-- title:
--   Proposition C.1 (Image of a pure state).
-- statement:
--   For $\ell\ge0$, $T^\ell(M)$ is the explicit $(\ell+1)$-dimensional normalized-monomial representation (C.9), evaluated on any complex $2\times2$ matrix. Its coordinates are indexed by $0,\ldots,\ell$. Let $V^\ell|w\rangle=|s_\ell(w)\rangle$ be the real Dicke embedding, $\Pi_\ell=V^\ell V^{\ell\dagger}$, and $|\psi^\ell\rangle=\sum_w\sqrt{\binom\ell w}\psi_0^{\ell-w}\psi_1^w|w\rangle$. Empty tensor powers are one-dimensional and $0^0=1$.
--
--   For every $\ell\ge0$ and arbitrary qubit vector $\psi$,
--   $$T^\ell(|\psi\rangle\langle\psi|)=|\psi^\ell\rangle\langle\psi^\ell|,\qquad\|\psi^\ell\|^2=(\|\psi\|^2)^\ell.$$
--   For $\ell>0$ the coherent ket is normalized exactly when $\psi$ is. At $\ell=0$, it is $[1]$ for every $\psi$, correcting the printed unrestricted normalization equivalence.
--
--   This supplies a concrete coordinate identity for the representation and symmetric-space constructions.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 60, Proposition C.1 (Image of a pure state).

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF p.60, Proposition C.1 and (C.21). PRINTED normalization iff at ell=0
is false at psi=0; CHANGED to exact norm formula for all ell and iff for ell>0.
WHY: the degree-zero vector is [1] for every psi. Independent moderation required. -/
theorem coherent_pure_image (ell : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    polynomialIrrep ell (pureDensity psi) = pureDensity (monomialKet ell psi) ∧
    ‖monomialKet ell psi‖^2 = (‖psi‖^2)^ell ∧
    (0 < ell → (IsState (monomialKet ell psi) ↔ IsState psi)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
