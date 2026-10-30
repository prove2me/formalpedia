-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_momentCompression
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.momentCompression
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:20:20.175473+00:00
-- url     : https://prove2.me/theorems/0f22d7f2-e29e-4107-8632-ee72debe49b8
-- title:
--   Nonzero proportionality of compressed stabilizer moments
-- statement:
--   Let $d$ be prime, $t\geq1$, and $N\geq n>0$. Write $M_{n,t}$ for the uniform pure-stabilizer density moment. Compress the last $N-n$ physical qudits in each copy onto the computational zero state. The resulting operator and $M_{n,t}$ are both nonzero and positively proportional; the source does not specify the proportionality constant.
--
--   $$
--   (I\otimes\langle0|^{\otimes(N-n)t})M_{N,t}(I\otimes|0\rangle^{\otimes(N-n)t})=cM_{n,t},\qquad c>0.
--   $$
--
--   This gives the source's nonzero proportionality of compressed stabilizer moments in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 46, lemma-5.2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.46, Lemma 5.2: both operators are nonzero and the proportionality scalar is positive. -/
theorem momentCompression (d N n t : ℕ) [NeZero d] [Fact (Nat.Prime d)]
    (ht : 1 ≤ t) (hn : 0 < n) (hN : n ≤ N) :
    compressZero hN (stabilizerMoment d N t) ≠ 0 ∧ stabilizerMoment d n t ≠ 0 ∧
    ∃ c : ℝ, 0 < c ∧ compressZero hN (stabilizerMoment d N t) =
      (c : ℂ) • stabilizerMoment d n t := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
