-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P22_qkdCriterion
-- name    : QAlgorithms.Papers.Independent.Support50.P22.qkdCriterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:50:55.351926+00:00
-- url     : https://prove2.me/theorems/400a4dd3-371c-415f-9160-0f7f59ecfbee
-- title:
--   QKD sufficient-security criterion (4)
-- statement:
--   Let $H=H_A\otimes H_B$ have dimension $d=ab$, where $a,b\ge1$, and let $n\ge0$. Fix a normalized purification $\psi_{H^nR}$ of the Hilbert–Schmidt de Finetti state. Let $E$ be the CPTP map induced by a QKD protocol, with classical outputs consisting of a finite length branch, two keys of that branch's length, and the full public transcript. Length zero is allowed. Define $S$ to preserve the length and transcript while replacing both keys by an identical uniform key of that length, and construct $F=S\circ E$. Suppose every input permutation has a CPTP output relabeling that gives covariance for both $E$ and $F$. For $\epsilon\ge0$,
--   $$
--   \|((E-F)\otimes\operatorname{id}_R)(|\psi\rangle\langle\psi|)\|_1
--   \le\frac{\epsilon}{(n+1)^{d^2-1}}
--   \quad\Longrightarrow\quad
--   \|E-F\|_\diamond\le\epsilon.
--   $$
--   This is the source's sufficient criterion for general security, with full norms and no hashing-shortening premise. The independent identical local measurements and classical processing enter through their induced channel $E$.
-- source:
--   Post-selection technique for quantum channels with applications to quantum cryptography, arXiv:0809.3019v1, PDF p. 3, Unnumbered QKD sufficient-security criterion, equation (4)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P22

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Dependency50.P18 (ClassicalOutput)

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P22.postselectionMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P22.postselectionMatrixBorelSpace

/-- QKD sufficient-security criterion, equation (4), PDF p.3 (not p.2).
H has dimension a*b for the Alice--Bob pair; all norm factors are full norms.
The same output channel witnesses covariance for E and the constructed F. -/
theorem qkdCriterion (n a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    {R L C : Type} [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype L] [DecidableEq L] [Nonempty L]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (len : L → ℕ)
    (psi : EuclideanSpace ℂ (Copies (Fin (a*b)) n × R))
    (hpsi : FinitePurification psi (deFinettiState n (a*b) (Nat.mul_pos ha hb)))
    (E : Matrix (Copies (Fin (a*b)) n) (Copies (Fin (a*b)) n) ℂ →ₗ[ℂ]
      Matrix (KeyOut L C len) (KeyOut L C len) ℂ)
    (hE : IsChannel E) (hclass : ClassicalOutput E)
    (hcov : ∀ pi : Equiv.Perm (Fin n), ∃ K : Superop (KeyOut L C len) (KeyOut L C len),
      IsChannel K ∧ (∀ X, E (permuteInput pi X) = K (E X)) ∧
      (∀ X, idealProtocol len E (permuteInput pi X) = K (idealProtocol len E X)))
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (htest : traceNorm (tensorId (E - idealProtocol len E) (pureDensity psi)) ≤
      epsilon / (n+1 : ℝ) ^ ((a*b)^2-1)) :
    diamond (E - idealProtocol len E) ≤ epsilon := by sorry

end QAlgorithms.Papers.Independent.Support50.P22

end
