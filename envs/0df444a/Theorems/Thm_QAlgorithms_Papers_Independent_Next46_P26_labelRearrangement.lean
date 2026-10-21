-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P26_labelRearrangement
-- name    : QAlgorithms.Papers.Independent.Next46.P26.labelRearrangement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:08:31.917505+00:00
-- url     : https://prove2.me/theorems/5f713c9e-25f3-42de-a58f-87a76c9793a3
-- title:
--   The explicit label rearrangement is a bijection
-- statement:
--   Fix a Young diagram $\lambda$. Labels $x_i$ and $y_j$ are tagged symbols. An element of $F_\lambda$ consists of a special pair $x_p,y_q$ for an occupied starting cell $(p,q)$ and, in every noncorner cell $(i,j)$, either $x_k$ with $i<k\le\lambda'_j$ or $y_l$ with $j<l\le\lambda_i$.
--
--   An element of $G_\lambda$ has special labels $x_r,y_s$ for a corner $(r,s)$. Noncorner cells off row $r$ and column $s$ retain the strict-hook label choices. In column $s$, cell $(i,s)$ permits $x_k$ for $i\le k\le r$ or $y_l$ for $s<l\le\lambda_i$. In row $r$, cell $(r,j)$ permits $x_k$ for $r<k\le\lambda'_j$ or $y_l$ for $j\le l\le s$.
--
--   Define $\phi$ by following the arrows encoded by the old labels from $(p,q)$ to its terminal corner $(r,s)$, and performing the rearrangement on p.5. Equivalently, the projected visited rows in column $s$ receive their own $x_i$ labels, projected visited columns in row $r$ receive their own $y_j$ labels, other visited cells receive the old label from their projection in the terminal column for vertical steps or terminal row for horizontal steps, and all other labels stay put. The special labels become $x_r,y_s$. Then
--   $$
--   \phi:F_\lambda\longrightarrow G_\lambda\quad\text{is a bijection}.
--   $$
--   This is the specific label rearrangement supporting equation (4). A corner start has no arrows; its special labels stay external. All shifts refer to the old arrangement.
-- source:
--   The weighted hook length formula, arXiv:1006.0043v1, PDF p. 5, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Lemma 1, pp.5–6: the particular label-rearrangement map of §2.2 is a
bijection from F_lambda onto G_lambda. BijOn includes membership of every image. -/
theorem labelRearrangement (lam : YoungDiagram) :
    Set.BijOn (rearrangeHookLabels lam) (hookLabelInputs lam) (hookLabelOutputs lam) := by sorry

end QAlgorithms.Papers.Independent.Next46.P26

end
