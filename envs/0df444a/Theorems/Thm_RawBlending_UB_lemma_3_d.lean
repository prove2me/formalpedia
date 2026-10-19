-- Prove2me | Theorems.Thm_RawBlending_UB_lemma_3_d
-- name    : RawBlending.UB.lemma_3_d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:27.523136+00:00
-- url     : https://prove2.me/theorems/c9e9e33e-113d-4d52-a61f-003df28879c3
-- title:
--   Lemma 3(d): backward preservation of H_t
-- statement:
--   Suppose $H_t$ holds at a period $1\le t\le T$. Then the preceding induction condition $H_{t-1}$ holds: $V_t$ is convex, continuous, and supermodular on $\mathbb R_+^2$, and its coordinatewise lower growth is bounded by the corresponding purchasing cost:
--   $$
--   \liminf_{x^j\to\infty}\frac{V_t(x)}{x^j}\ge c_t^j,\qquad j=1,2.
--   $$
--   This is the backward step for the structural properties of the value function.
--
--   **Formalization Note** The lower limit is expressed by an eventual lower bound for every positive error, with the other coordinate fixed and nonnegative. The model’s standing sign assumptions are explicit.
-- source:
--   Chen, Duenyas & Jasin, Optimal use and replenishment of two substitutable raw materials, SSRN working paper 2801786 (version of 2016-06-28), p. 11 (PDF 11), Lemma 3(d)

import Mathlib
import Definitions.Def_RawBlending_UB_Model

namespace RawBlending.UB

theorem lemma_3_d (d : Data) (hd : d.Standing) (t : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ d.T) (hH : H d t) : H d (t-1) := by sorry

end RawBlending.UB
