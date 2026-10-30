-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P19_bipartite_orthogonal_normal_form
-- name    : QAlgorithms.Papers.Independent.Advance50.P19.bipartite_orthogonal_normal_form
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:57:27.274818+00:00
-- url     : https://prove2.me/theorems/f7b4e416-6883-4a38-9446-7dc549596ced
-- title:
--   Bipartite Gaussian-unitary normal form
-- statement:
--   Let $n,k\ge0$ and $m=n+k$. Let $O\in SO(2n+2m)$ be the phase-space representation of a Gaussian unitary, grouped into $2n$ system and $2m$ environment directions. There exist orthogonal $Q_1,R_1\in O(2n)$, $Q_2,R_2\in O(2m)$, and a diagonal $D\in\mathbb R^{2n\times2n}$ with entries in $[0,1]$ such that
--
--   $$O=(Q_1\oplus Q_2)\begin{pmatrix}D&\sqrt{I-D^2}&0\\-\sqrt{I-D^2}&D&0\\0&0&I_{2k}\end{pmatrix}(R_1\oplus R_2).$$
--
--   The four local factors may contain reflections. This identifies the interacting environment directions and the $2k$ spectator directions.
-- source:
--   Degradability of Fermionic Gaussian Channels, arXiv:1604.01954v2, PDF p. 7, Lemma S2

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P19

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.7, Lemma S2. SOURCE CORRECTION C2: D has 2n by 2n entries,
not the printed n by n. The four local factors are orthogonal; reflections
are permitted. The environment has n+k modes and the spectator block 2k. -/
theorem bipartite_orthogonal_normal_form (n k : ℕ)
    (O : Matrix (Major n ⊕ (Major n ⊕ Major k))
      (Major n ⊕ (Major n ⊕ Major k)) ℝ)
    (hO : IsPhaseOrthogonal O) (hdet : O.det = 1) :
    ∃ (Q1 R1 : Matrix (Major n) (Major n) ℝ)
      (Q2 R2 : Matrix (Major n ⊕ Major k) (Major n ⊕ Major k) ℝ)
      (d : Major n → ℝ),
      IsPhaseOrthogonal Q1 ∧ IsPhaseOrthogonal R1 ∧ IsPhaseOrthogonal Q2 ∧ IsPhaseOrthogonal R2 ∧
      (∀ i, 0 ≤ d i ∧ d i ≤ 1) ∧
      O = Matrix.fromBlocks Q1 0 0 Q2 *
        Matrix.fromBlocks (Matrix.diagonal d)
          (Matrix.fromCols (Matrix.diagonal (fun i => Real.sqrt (1 - d i ^ 2))) 0)
          (Matrix.fromRows (-Matrix.diagonal (fun i => Real.sqrt (1 - d i ^ 2))) 0)
          (Matrix.fromBlocks (Matrix.diagonal d) 0 0 1) *
        Matrix.fromBlocks R1 0 0 R2 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P19

end
