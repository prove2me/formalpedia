-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_repeatedValueEntryOracle
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.repeatedValueEntryOracle
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:25:17.865086+00:00
-- url     : https://prove2.me/theorems/7163029b-91fa-4632-8b41-22d32f59c0ee
-- title:
--   Appendix A.3: repeated-value implementation of the sparse-access entry oracle (94)
-- statement:
--   Let an explicitly supplied reversible reverse map compute, from row and column indices $(i,j)$, either an occurrence label $(t,m)$ or a fixed zero sentinel. Let each of the $D$ active table entries have a specified $b$-bit code, with zero codes on all other physical data labels. Require a concrete clean-work arithmetic circuit implementing the reverse map; no efficient inversion is inferred from forward position formulas.
--
--   Compute the label, XOR its data code into a general output buffer, and uncompute the label. This unitary implements
--   $$ |i,j,y,0\rangle\longmapsto |i,j,y\mathbin\oplus\mathrm{code}(A_{ij}),0\rangle. $$
--   It loads $D$ items. If the given reverse computation has Toffoli count at most $B$, its compute/uncompute contribution is at most $2B$. Thus any uniform polylogarithmic arithmetic bound is preserved. Finite codes are the prescribed representations, rather than exact binary expressions for arbitrary reals.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 26, Appendix A.3: repeated-value implementation of the sparse-access entry oracle (94)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

local instance : DecidableEq QAlgorithms.Gate := Classical.decEq _

/-- PDF p.26, (93)-(94): repeated-value implementation of the sparse-access
entry oracle. A given cost-bearing reverse-map circuit is required explicitly.
Its compute/uncompute overhead doubles, so any uniform polylogarithmic bound
for that circuit remains such a bound with twice the same constant. Data is
an arbitrary specified b-bit representation, not an exact code of every real. -/
theorem repeatedValueEntryOracle (n d m b work : ℕ)
    (r : (Fin (2 ^ n) × Fin (2 ^ n)) → Option (Fin (2 ^ d) × Fin (2 ^ m)))
    (code : Fin (2 ^ d) → QAlgorithms.Qubits b)
    (active : Finset (Fin (2 ^ d)))
    (hcode : ∀ j, j ∉ active → code j = 0)
    (hrange : ∀ ij l, r ij = some l → l.1 ∈ active)
    (c : List (ArithmeticGate ((n + n + (1 + d + m)) + work)))
    (hc : RealizesMap rowColumnLabelBits rowColumnLabelBits
      (fun x : (Fin (2 ^ n) × Fin (2 ^ n)) × QAlgorithms.Qubits (1 + d + m) =>
        (x.1, x.2 + reverseCode r x.1)) (n + n + (1 + d + m)) work c) :
    entryCircuit r code ∈ Matrix.unitaryGroup _ ℂ ∧
    (∀ (ij : Fin (2 ^ n) × Fin (2 ^ n)) (y : QAlgorithms.Qubits b),
      QAlgorithms.act (entryCircuit r code) (QAlgorithms.ket ((y, ij), 0)) =
        QAlgorithms.ket ((y + (match r ij with | none => 0 | some l => code l.1), ij), 0)) ∧
    loadingCost (baseLoadingSchedule active.card) = active.card ∧
    (∀ bound : ℝ, (toffoliCount c : ℝ) ≤ bound →
      (entryArithmeticCost c : ℝ) ≤ 2 * bound) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
