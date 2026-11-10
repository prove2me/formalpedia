-- Prove2me | Theorems.Thm_SivanLPTensor_Recovery_alternating_properties
-- name    : SivanLPTensor.Recovery.alternating_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T05:32:59.442754+00:00
-- url     : https://prove2.me/theorems/160a59af-7b26-4ced-9a92-8a71236e4462
-- title:
--   Lemma 2.1 — Basic properties of alternating representations
-- statement:
--   Let $X=\mathbb R^D$, $m=d+2\ge3$, $E=[e_1|\cdots|e_m]$ be arbitrary columns, and $P$ a $d$-row covector frame, without an independence requirement. For every square matrix $M$,
--   $$\operatorname{Alt}(EM)=\det(M)\operatorname{Alt}(E).$$
--   When $M$ is invertible the spans of these alternating tensors coincide. In addition,
--   $$\iota_P\operatorname{Alt}(E)=\sum_{j<k}(-1)^{j+k+1}\det(PE[\widehat{j,k}])\operatorname{Alt}(E[j,k]).$$
--   This supplies both the change-of-basis rule and the coordinate formula used in the contraction routines. Neither $E$ nor $M$ is assumed nonsingular for the identities.
--
--   Differences from the source:
--   - encoding: finite real modes and one-based indices → dependent Fin coordinates with zero-based indices; reason: the same finite arrays; parity in the signed minor formula is unchanged
-- source:
--   Shiri Sivan, STOC 2027 submission #1294 (October 2026), Lemma 2.1, printed p. 5 / PDF p. 7, (3)

import Definitions.Def_SivanLPTensor_Recovery_geometryModel

namespace SivanLPTensor.Recovery
open scoped BigOperators

theorem alternating_properties {D d : ℕ} (hd : 1 ≤ d)
    (E : Matrix (Fin D) (Fin (d + 2)) ℝ) :
    (∀ M : Matrix (Fin (d + 2)) (Fin (d + 2)) ℝ,
      alt (E * M) = Matrix.det M • alt E) ∧
    (∀ M : Matrix (Fin (d + 2)) (Fin (d + 2)) ℝ, Matrix.det M ≠ 0 →
      Submodule.span ℝ {alt (E * M)} = Submodule.span ℝ {alt E}) ∧
    ∀ P : Matrix (Fin d) (Fin D) ℝ, contract P (alt E) = minorContraction P E := by sorry

end SivanLPTensor.Recovery
