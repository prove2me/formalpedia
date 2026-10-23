-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_genericKrausGram
-- name    : QAlgorithms.Papers.Independent.Information100.P44.genericKrausGram
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:29:32.629635+00:00
-- url     : https://prove2.me/theorems/e4728bcd-4dd6-4d0d-87ef-ab9bfb0e684e
-- title:
--   Theorem 1: generic Kraus–Gram representation
-- statement:
--   Let $d\ge1$ and let $K_1,\ldots,K_N$ be arbitrary complex $d\times d$ matrices, allowing $N=0$. Put $\Phi(X)=\sum_a K_aXK_a^\dagger$, $v_{r|i}=((K_a)_{ri})_a$, and $p(r|i)=\Phi(|i\rangle\langle i|)_{rr}$. With the inner product conjugate-linear in its first argument,
--   $$p(r|i)=\|v_{r|i}\|^2,\qquad \Phi(|i\rangle\langle j|)_{rs}=\langle v_{s|j},v_{r|i}\rangle,\qquad |\Phi(|i\rangle\langle j|)_{rs}|\le\sqrt{p(r|i)p(s|j)}.$$
--   For two nonzero vectors, equality in the last bound is equivalent to complex collinearity. The vectors need no normalization, and trace preservation is not assumed. These identities express CP coherence transfers as Gram data.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 6, Theorem 1: generic Kraus–Gram representation

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.6, Theorem 1: generic Kraus–Gram representation and sharp Cauchy–Schwarz. -/
theorem genericKrausGram {d n : ℕ} (hd : 0 < d) (K : Fin n → Mat d) :
    (∀ r i, (krausApply K (matrixUnit i i) r r : ℂ) =
      (‖krausVector K r i‖ ^ 2 : ℝ)) ∧
    (∀ i j r s, krausApply K (matrixUnit i j) r s =
      inner ℂ (krausVector K s j) (krausVector K r i)) ∧
    (∀ i j r s, ‖krausApply K (matrixUnit i j) r s‖ ≤
      Real.sqrt (population (krausApply K) r i * population (krausApply K) s j)) ∧
    (∀ i j r s, krausVector K r i ≠ 0 → krausVector K s j ≠ 0 →
      (‖krausApply K (matrixUnit i j) r s‖ =
        Real.sqrt (population (krausApply K) r i * population (krausApply K) s j) ↔
          Collinear (krausVector K r i) (krausVector K s j))) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
