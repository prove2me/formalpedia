-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P57_parameter_description
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P57.parameter_description
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:08:42.282495+00:00
-- url     : https://prove2.me/theorems/6c4ca3a3-e39f-405b-958f-e3e326fe2461
-- title:
--   Main properties: polynomial-size parameter description
-- statement:
--   For a chain of $N\ge1$ qubits and bond dimension $D\ge1$, store the real and imaginary parts of the two complex site matrices, one real graph weight for each unordered pair, and all real and imaginary entries of each local $2\times2$ unitary. This description is injective on the admissible data and uses
--
--   $$P(N,D)=4ND^2+\frac{N(N-1)}2+8N$$
--
--   real entries. In particular, there is an absolute constant $C>0$, independent of $N,D$ and of all numerical data, such that
--
--   $$P(N,D)\le C(ND^2+N^2).$$
--
--   This is a description-size statement in $N$ and $D$. The unitary, graph-symmetry and angle constraints remain imposed; the count does not concern independent manifold coordinates or finite-precision bit storage.
-- source:
--   Renormalization algorithm with graph enhancement, arXiv:0802.1211v1, PDF p. 2, Main properties: polynomial-size parameter description

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P57

noncomputable section

open scoped ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Intakethird100.P57

attribute [local instance] Classical.propDecidable

/-- PDF p.2, Main properties: an injective description with an absolute uniform bound.
This counts real entries, not intrinsic coordinates or bounded-precision bits. -/
theorem parameter_description :
    (∀ (N D : ℕ), 1 ≤ N → 1 ≤ D → Function.Injective (@describe N D)) ∧
    (∀ (N D : ℕ), 1 ≤ N → 1 ≤ D → Fintype.card (DescriptionIndex N D) =
      4 * N * D ^ 2 + N * (N - 1) / 2 + 8 * N) ∧
    (∃ C : ℕ, 0 < C ∧ ∀ N D : ℕ, 1 ≤ N → 1 ≤ D →
      Fintype.card (DescriptionIndex N D) ≤ C * (N * D ^ 2 + N ^ 2)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P57

end
