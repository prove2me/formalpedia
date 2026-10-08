-- Prove2me | Theorems.Thm_PatakiRank_Mult_lemma_4_2
-- name    : PatakiRank.Mult.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:31.513923+00:00
-- url     : https://prove2.me/theorems/4071b165-9df7-4f4f-8a4c-15b44ceee2b7
-- title:
--   Lemma 4.2, p. 349 — for an extreme point x* of Θ, F* = {x*} × Ω_k(A(x*)) is a face of the feasible set of (4.26)
-- statement:
--   Let $A_0,A_1,\dots,A_m$ be linearly independent symmetric $n\times n$ matrices, $A(x)=A_0+\sum_{i=1}^mx_iA_i$, $m\ge1$ and $1\le k<n$. Let $\Theta$ be the set of optimal solutions of $(EV_k)\ \min\{f_k(A(x)):x\in\mathbb R^m\}$, and let $\Phi$ be the feasible set of the SDP
--   $$\min_{x,z,V,W}\ kz+I\bullet V\quad\text{s.t.}\quad V,W\succeq0,\quad zI+V-W=A(x). \tag{4.26}$$
--   If $x^*$ is an extreme point of $\Theta$, then
--   $$F^*=\{x^*\}\times\Omega_k(A(x^*))$$
--   is a face of $\Phi$.
--
--   This lets the face rank bound of Theorem 2.2 be applied to the optimal slack matrices $V,W$ at an extreme minimizer of $f_k\circ A$.
--
--   **Formalization Note** The hypotheses are the standing assumptions of §4 (symmetry and linear independence of $A_0,\dots,A_m$, $m\ge1$, $k<n$) plus $k\ge1$ from p. 340; the proof uses only symmetry and $1\le k<n$.
-- source:
--   Pataki, On the rank of extreme matrices in semidefinite programs and the multiplicity of optimal eigenvalues, Math. Oper. Res. 23(2) (1998), p. 349, Lemma 4.2

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_PatakiRank_Mult_Setting
open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral

namespace PatakiRank.Mult

/-- Lemma 4.2 (p. 349): under the standing assumptions of §4, if `x*` is an extreme point of
`Θ`, then `F* = {x*} × Ω_k(A(x*))` is a face of the feasible set of (4.26). -/
theorem lemma_4_2 {n m k : ℕ} (A0 : Matrix (Fin n) (Fin n) ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA0 : A0.IsSymm) (hA : ∀ i, (A i).IsSymm)
    (hind : LinearIndependent ℝ (Fin.cons A0 A : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ))
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hkn : k < n)
    (xs : Fin m → ℝ) (hx : IsExtremePt (Theta k A0 A) xs) :
    IsFace (feas426 A0 A) (Fstar k A0 A xs) := by sorry

end PatakiRank.Mult
