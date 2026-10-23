-- Prove2me | Theorems.Thm_QuadMemory_ConvexOpt_lemma_12
-- name    : QuadMemory.ConvexOpt.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:54.807926+00:00
-- url     : https://prove2.me/theorems/fd4cd192-9380-42f4-8f18-3a89b922ab3b
-- title:
--   Lemma 12, p. 22 — a uniform hypercube vector is t-orthogonal to k orthonormal vectors with probability at most 2^{−c_H k}
-- statement:
--   There is an absolute constant $c_H>0$ such that the following holds. Let $h\sim\mathcal U(\{\pm1\}^d)$. For any $t\in(0,1/2]$ and any matrix $Z=[z_1,\dots,z_k]\in\mathbb R^{d\times k}$ with orthonormal columns,
--   $$\mathbb P\big(\|Z^\top h\|_\infty\le t\big)\le2^{-c_Hk}.$$
--
--   The rows of the hidden matrix $A$ are such vectors, so a Player who knows little about $A$ cannot produce many robustly independent vectors nearly orthogonal to all its rows. This is the concentration half of Proposition 14.
--
--   **Formalization Note.** The paper cites this from Marsden, Sharan, Sidford and Valiant (2022). The constant is packaged as the predicate `IsHypercubeConst`, which Proposition 14 takes as a hypothesis on $c_H$.
-- source:
--   Blanchard, Zhang & Jaillet, arXiv:2302.04963v2, p. 22, Lemma 12 (citing Marsden, Sharan, Sidford & Valiant 2022)

import Mathlib
import Definitions.Def_QuadMemory_ConvexOpt_Model
import Definitions.Def_QuadMemory_ConvexOpt_Game

namespace QuadMemory.ConvexOpt

/-- Lemma 12 (p. 22, from Marsden–Sharan–Sidford–Valiant 2022): there is an absolute constant
`c_H > 0` such that for `h` uniform on `{±1}^d`, any `t ∈ (0, 1/2]` and any `Z ∈ ℝ^{d×k}` with
orthonormal columns, `P(‖Zᵀh‖_∞ ≤ t) ≤ 2^{-c_H k}`. -/
theorem lemma_12 : ∃ c : ℝ, 0 < c ∧ IsHypercubeConst c := by sorry

end QuadMemory.ConvexOpt
