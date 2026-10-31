-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_collectiveZBinaryFormula
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.collectiveZBinaryFormula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:01:50.18812+00:00
-- url     : https://prove2.me/theorems/017805a8-57ff-4270-a258-cc4d2c574948
-- title:
--   The binary diagonal formula for collective F_z
-- statement:
--   Let $n\ge1$ and define $F_z=\frac12\sum_{\ell=1}^n Z_\ell$, with identities on the other qubits. For a computational basis string $b=(b_1,\ldots,b_n)$, including leading zeroes,
--
--   $$F_z=\operatorname{diag}\left(\frac12\sum_{\ell=1}^n(-1)^{b_\ell}\right)_b.$$
--
--   Equivalently the $i$th diagonal entry in the paper's one-based indexing is obtained from the $n$-digit binary expansion of $i-1$. The formal index conversion uses the fixed most-significant-bit-first equivalence. This explicit formula keeps both the factor $1/2$ and all $n$ digits.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 16, Lemma 8: binary formula for collective F_z

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- Lemma 8, PDF p.16, (86)–(89): n binary digits, including leading
zeroes, and the essential factor 1/2. Bit order is the frozen MSB convention;
the diagonal sum itself is invariant under reversing the bit order. -/
theorem collectiveZBinaryFormula {n : ℕ} (hn : 0 < n) :
    collectiveZ n = Matrix.diagonal (fun b : QAlgorithms.Qubits n =>
      (1 / 2 : ℂ) * ∑ k : Fin n, if b k then (-1 : ℂ) else 1) ∧
    (∀ i : Fin (2 ^ n),
      collectiveZ n ((QAlgorithms.bitsEquivFin n).symm i) ((QAlgorithms.bitsEquivFin n).symm i) =
        (1 / 2 : ℂ) * ∑ k : Fin n,
          if ((QAlgorithms.bitsEquivFin n).symm i) k then (-1 : ℂ) else 1) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
