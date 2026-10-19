-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_isometric_encoding
-- name    : QAlgorithms.Papers.Independent.Information100.P62.isometric_encoding
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:36:13.104458+00:00
-- url     : https://prove2.me/theorems/34d889df-9691-41a6-befc-59aa493d775d
-- title:
--   Unnumbered isometric encoder equivalence (3.6)–(3.7)
-- statement:
--   For the standard logical space $L=\bigoplus_k\mathbb C^{d_k}$ of a nonzero algebra $A$, exact transmission through $\Phi$ is equivalent to existence of an isometry $V:L\to H$ and decoding channel $D$ with
--   $$V^*S_\Phi V\subseteq\bigoplus_k\mathbb CI_{d_k},\qquad D\circ\Phi\circ(X\mapsto VXV^*)=P_A.$$
--   The second equality holds on the full matrix algebra. One copy of each simple block suffices.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 24, Unnumbered isometric encoder equivalence (3.6)–(3.7)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.24, Unnumbered isometric encoder equivalence (3.6)–(3.7). -/
theorem isometric_encoding [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Valid A) :
    Transmits F A ↔ ∃ V : Matrix I (Logical A) ℂ, Vᴴ * V = 1 ∧
      (∀ s ∈ graph F, Vᴴ * s * V ∈ pinchingSystem A) ∧
      ∃ D : Superop O (Logical A), IsChannel D ∧ D ∘ F ∘ conjSuperop V = pinching A := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
