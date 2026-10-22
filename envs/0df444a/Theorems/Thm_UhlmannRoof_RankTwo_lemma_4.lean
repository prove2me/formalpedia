-- Prove2me | Theorems.Thm_UhlmannRoof_RankTwo_lemma_4
-- name    : UhlmannRoof.RankTwo.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:23.789959+00:00
-- url     : https://prove2.me/theorems/88148e1c-297b-4ebe-8b61-eae526dec9ed
-- title:
--   Lemma 4, p. 7 — zero entropy of the diagonal algebra implies purity
-- statement:
--   Let $\omega$ be a state of the full matrix algebra relative to its diagonal maximal commutative subalgebra. If its entropy is zero, then it is pure:
--   $$H_\omega=\widetilde S(\omega)-R(\omega)=0\quad\Longrightarrow\quad\omega\text{ is pure}.$$
--   This links vanishing entropy of the restriction problem to extremality of the original state.
--
--   **Formalization Note** The diagonal algebra is maximal commutative. The hypothesis that $\omega$ is a state is explicit.
-- source:
--   Uhlmann, arXiv:quant-ph/9704017v2, p. 7, Lemma 4

import Mathlib
import Definitions.Def_UhlmannRoof_RankTwo_Model

namespace UhlmannRoof.RankTwo

/-- Uhlmann, Lemma 4, p. 7: zero entropy of the diagonal algebra
forces the state to be pure. -/
theorem lemma_4 {d : ℕ} (ω : Mat d) (hω : IsState ω) (hzero : H ω = 0) :
    IsPure ω := by sorry

end UhlmannRoof.RankTwo
