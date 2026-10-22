-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_symmetric_projector_formulas
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.symmetric_projector_formulas
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:59:58.364477+00:00
-- url     : https://prove2.me/theorems/193478c3-0c9e-4cc9-b7ed-21b00dc9e937
-- title:
--   Lemma D.1.
-- statement:
--   For $\ell\ge0$, $T^\ell(M)$ is the explicit $(\ell+1)$-dimensional normalized-monomial representation (C.9), evaluated on any complex $2\times2$ matrix. Its coordinates are indexed by $0,\ldots,\ell$. Let $V^\ell|w\rangle=|s_\ell(w)\rangle$ be the real Dicke embedding, $\Pi_\ell=V^\ell V^{\ell\dagger}$, and $|\psi^\ell\rangle=\sum_w\sqrt{\binom\ell w}\psi_0^{\ell-w}\psi_1^w|w\rangle$. Empty tensor powers are one-dimensional and $0^0=1$.
--
--   For every $\ell\ge0$, normalized uniform pure-qubit measure $d\psi$ gives
--   $$\Pi_\ell=\frac1{\ell!}\sum_{\pi\in S_\ell}P(\pi)=(\ell+1)\int (|\psi\rangle\langle\psi|)^{\otimes\ell}\,d\psi.$$
--   The projector is defined from the Dicke columns. All three expressions are the one-dimensional identity at $\ell=0$.
--
--   This supplies a concrete coordinate identity for the representation and symmetric-space constructions.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 65, Lemma D.1.

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

/-- PDF p.65, Lemma D.1: all three projector formulas, including ell=0. -/
theorem symmetric_projector_formulas (ell : ℕ) :
    dickeColumnProjector ell = (1 / (Nat.factorial ell : ℂ)) •
      ∑ p : Equiv.Perm (Fin ell),
        (fun x y : Qubits ell => if x = (fun i => y (p.symm i)) then (1:ℂ) else 0) ∧
    dickeColumnProjector ell = ((ell : ℂ)+1) •
      (fun x y => ∫ psi : EuclideanSpace ℂ (Fin 2),
        (pureDensity (QAlgorithms.Papers.Independent.Support21.P18.physicalPower ell psi)) x y
          ∂QAlgorithms.Papers.Independent.Support21.P18.pureLaw) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
