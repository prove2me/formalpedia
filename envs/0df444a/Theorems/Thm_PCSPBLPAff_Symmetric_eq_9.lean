-- Prove2me | Theorems.Thm_PCSPBLPAff_Symmetric_eq_9
-- name    : PCSPBLPAff.Symmetric.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:21.477725+00:00
-- url     : https://prove2.me/theorems/01f1675e-8a71-4398-900c-8bac67e4ba64
-- title:
--   Eq. (9), proof of Theorem 2, p. 7 — W_i(a) = Σ_{y|i=a} P_j(y)
-- statement:
--   Let $(w,p)$ solve $\mathrm{LP}_{\mathbb Q}(X,\mathbf A)$, $(r,q)$ solve $\mathrm{Aff}_{\mathbb Z}(X,\mathbf A)$, and $u,\ell,v\in\mathbb N$. For every constraint $c_j$, every position $k$ of its scope, with $x_i$ the $k$-th variable of $\bar x_j$, and every $a\in A$,
--   $$
--   u\ell\,w_i(a)+v\,r_i(a)=\sum_{y:\ y_k=a}\bigl(u\ell\,p_j(y)+v\,q_j(y)\bigr).
--   $$
--
--   In the notation of the proof this is $W_i(a)=\sum_{y\in R_j^{\mathbf A},\,y|i=a}P_j(y)$: in the matrix with $P_j(y)$ rows equal to $y$, the symbol $a$ appears exactly $W_i(a)$ times in the column of $x_i$.
--
--   **Formalization Note** The page writes $p_i(y)$, $q_i(y)$ in the middle line of (9) for $p_j(y)$, $q_j(y)$. The sum runs over all tuples, which equals the sum over $R_j^{\mathbf A}$ because $p_j,q_j$ vanish off it.
-- source:
--   arXiv:1907.04383v3, proof of Theorem 2, p. 7, Eq. (9)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

namespace PCSPBLPAff.Symmetric

/-- Eq. (9), proof of Theorem 2, p. 7: for every constraint `j`, position `k` of its scope and
`a ∈ A`, `uℓ w_i(a) + v r_i(a) = Σ_{y, y_k = a} (uℓ p_j(y) + v q_j(y))` where `x_i` is the
`k`-th variable of `x̄_j`. -/
theorem eq_9 {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (X : Instance τ ar) (𝔸 : RelStruct τ ar A) (w : Fin X.n → A → ℚ)
    (p : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ) (r : Fin X.n → A → ℤ)
    (q : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℤ)
    (hLP : IsLPSol X 𝔸 w p) (hAff : IsAffSol X 𝔸 r q) (u ℓ v : ℕ) :
    ∀ (j : Fin X.m) (k : Fin (ar (X.sym j))) (a : A),
      ((u : ℚ) * ℓ * w (X.scope j k) a + v * r (X.scope j k) a) =
        ∑ y ∈ Finset.univ.filter (fun y : Fin (ar (X.sym j)) → A => y k = a),
          ((u : ℚ) * ℓ * p j y + v * q j y) := by sorry

end PCSPBLPAff.Symmetric
