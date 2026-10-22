-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P28_gz_tableau_encoding
-- name    : QAlgorithms.Papers.Independent.Gap48.P28.gz_tableau_encoding
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:28:46.062891+00:00
-- url     : https://prove2.me/theorems/895ca333-eebd-4f14-8cb8-348c64b53953
-- title:
--   GZ chains correspond to semistandard tableaux with a cellwise binary encoding
-- statement:
--   Let $n,d\ge1$ and fix a Young shape $\lambda$ with exactly $n$ cells and at most $d$ rows. For a bounded GZ chain with top shape $\lambda$, label each cell by the first level containing it. With the zero-based alphabet $\{0,\ldots,d-1\}$, this is a semistandard tableau, and every semistandard tableau comes from exactly one such chain. Encoding each cell symbol with $\lceil\log_2 d\rceil$ most-significant-bit-first binary digits is injective and uses exactly $n\lceil\log_2 d\rceil$ wires. The shape is fixed separately. When $d=1$, the unique tableau uses zero symbol wires.
-- source:
--   The Quantum Schur Transform: I. Efficient Qudit Circuits, arXiv:quant-ph/0601001v1, PDF p. 11, III B: tableau encoding, following Eq.(23)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P28

open scoped Matrix Kronecker ComplexConjugate

/-- PDF p.11, §III B: GZ chains of a fixed top shape correspond bijectively
to semistandard tableaux by labelling each cell when it first appears.
The alternative tableau code is injective and has n ceil(log_2 d) wires.
Ceilings restore integer wire counts suppressed by the source. The shape
is fixed throughout, including when d=1 gives a zero-bit symbol code. -/
theorem gz_tableau_encoding (n d : ℕ) (hn : 1 ≤ n) (hd : 0 < d)
    (lambda : QAlgorithms.Schur.Partition d n) :
    (∀ q : GZPattern n d,
      (∀ c : Fin d, (q.val ⟨d - 1, by omega⟩ c).val = lambda.val.rowLen c.val) →
      QAlgorithms.Schur.IsSemistandardFilling lambda (gzTableau lambda hd q)) ∧
    (∀ t : lambda.val.cells → Fin d,
      QAlgorithms.Schur.IsSemistandardFilling lambda t →
      ∃! q : GZPattern n d,
        (∀ c : Fin d, (q.val ⟨d - 1, by omega⟩ c).val = lambda.val.rowLen c.val) ∧
        gzTableau lambda hd q = t) ∧
    Function.Injective (fun t : {t : lambda.val.cells → Fin d //
      QAlgorithms.Schur.IsSemistandardFilling lambda t} => tableauBinaryCode lambda t.val) ∧
    Fintype.card (lambda.val.cells × Fin (Nat.clog 2 d)) =
      n * Nat.clog 2 d := by sorry

end QAlgorithms.Papers.Independent.Gap48.P28

end
