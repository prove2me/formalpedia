-- Prove2me | Theorems.Thm_SteuerChoo_Lexico_mem_Phi_unique_of_nondominated
-- name    : SteuerChoo.Lexico.mem_Phi_unique_of_nondominated
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:52:17.960985+00:00
-- url     : https://prove2.me/theorems/cbb929b4-2701-4c36-a139-cfd3005c3e11
-- title:
--   Proof of Theorem 4.5 — $\bar z\in\Phi(\hat\alpha)$, and no other nondominated $z$ lies in $\Phi(\hat\alpha)$
-- statement:
--   Let $Z\subseteq\mathbb R^k$ ($k\ge1$) be a set of criterion vectors with nondominated set $N$, let $z^*$ be an ideal criterion vector for $Z$, and let $\bar z\in N$. Let $\bar\lambda$ be the weights of eq. (4.3) for $\bar z$, and let $\hat\alpha$ be the minimal value of the weighted Tchebycheff program with weights $\bar\lambda$, i.e. the least value of $\max_i\bar\lambda_i(z^*_i-z_i)$ over $z\in Z$. With
--   $$
--   \Phi(\hat\alpha)=\{z\in\mathbb R^k \mid z_i\ge z^*_i-\hat\alpha/\bar\lambda_i \text{ when } \bar\lambda_i>0\},
--   $$
--   we have
--   $$
--   \bar z\in\Phi(\hat\alpha)\qquad\text{and}\qquad z\in N\cap\Phi(\hat\alpha)\ \Longrightarrow\ z=\bar z .
--   $$
--
--   This is the key step in the proof of Theorem 4.5: among nondominated vectors, $\bar z$ is the only one reached by the first stage of the lexicographic program with weights $\bar\lambda$. Dominated vectors may also lie in $\Phi(\hat\alpha)$; removing them is the task of the second stage.
--
--   **Formalization Note** $Z$ is an arbitrary set (no finiteness or compactness is assumed). The existence of the minimum $\hat\alpha$ is taken as the hypothesis that $\hat\alpha$ is the least element of the image of $Z$ under the first-stage objective. The claim is stated for $z\in N$ only, as on the page; the paper's next sentence ("the associated weighted Tchebycheff program has a unique solution") is not formalized, because a dominated vector $z$ with $z_j=z^*_j=\bar z_j$ can tie with $\bar z$ in the first stage (e.g. $Z=\{(5,3),(5,1),(1,10)\}$, $z^*=(5,10)$, $\bar z=(5,3)$, $\bar\lambda=(1,0)$).
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983), pp. 335-336, proof of Theorem 4.5, first three sentences

import Mathlib
import Definitions.Def_SteuerChoo_Lexico_nondominated
import Definitions.Def_SteuerChoo_Lexico_IsIdealVector
import Definitions.Def_SteuerChoo_Lexico_tcheb
import Definitions.Def_SteuerChoo_Lexico_lamBar
import Definitions.Def_SteuerChoo_Lexico_Phi

namespace SteuerChoo.Lexico

theorem mem_Phi_unique_of_nondominated {k : ℕ} [NeZero k]
    (Z : Set (Fin k → ℝ)) (zstar zbar : Fin k → ℝ) (αhat : ℝ)
    (hideal : IsIdealVector Z zstar) (hzbar : zbar ∈ nondominated Z)
    (hα : IsLeast (tcheb (lamBar zstar zbar) zstar '' Z) αhat) :
    zbar ∈ Phi (lamBar zstar zbar) zstar αhat ∧
      ∀ z ∈ nondominated Z, z ∈ Phi (lamBar zstar zbar) zstar αhat → z = zbar := by sorry

end SteuerChoo.Lexico
