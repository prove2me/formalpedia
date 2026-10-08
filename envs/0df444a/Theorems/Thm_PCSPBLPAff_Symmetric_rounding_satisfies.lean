-- Prove2me | Theorems.Thm_PCSPBLPAff_Symmetric_rounding_satisfies
-- name    : PCSPBLPAff.Symmetric.rounding_satisfies
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:36.333608+00:00
-- url     : https://prove2.me/theorems/dd8f96c9-0b32-421d-8362-cdcae066355b
-- title:
--   Proof of Theorem 2, p. 7 — X_i := f(a,…,a [W_i(a) times]) is a satisfying assignment of X in B
-- statement:
--   Let $f:A^L\to B$ be a symmetric polymorphism of $(\mathbf A,\mathbf B)$. Let $W_i(a)\in\mathbb N$ ($i\in[n]$, $a\in A$) and $P_j(y)\in\mathbb N$ ($j\in[m]$, $y\in A^{\mathrm{ar}(R_j)}$) satisfy
--
--   1. $P_j(y)=0$ for $y\notin R_j^{\mathbf A}$;
--   2. $\sum_y P_j(y)=L$ for every $j$;
--   3. $W_i(a)=\sum_{y:\,y_k=a}P_j(y)$ whenever $x_i$ is the $k$-th variable of $\bar x_j$ (Eq. (9)).
--
--   Let $x^{(i)}\in A^L$ be any tuple in which each $a\in A$ occurs exactly $W_i(a)$ times. Then the assignment
--   $$
--   X_i := f\bigl(x^{(i)}\bigr)=f(\dots,\underbrace{a,\dots,a}_{W_i(a)\text{ times }\forall a\in A},\dots)
--   $$
--   satisfies every constraint of $X$ in $\mathbf B$: $(X_i)_{x_i\in\bar x_j}\in R_j^{\mathbf B}$ for every $j$.
--
--   This is the soundness step of Theorem 2: from the integer counts produced by the LP and the affine solution it builds a solution in $\mathbf B$.
--
--   **Formalization Note** The counts are hypotheses, so the statement does not depend on how they were obtained. By symmetry of $f$ the value $X_i$ does not depend on the order of the entries of $x^{(i)}$, which is why any tuple with the right counts is allowed.
-- source:
--   arXiv:1907.04383v3, proof of Theorem 2, p. 7, from "We claim that the assignment" and the paragraph after Eq. (9)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

namespace PCSPBLPAff.Symmetric

/-- Proof of Theorem 2, p. 7: let `f` be a symmetric polymorphism of arity `L`, and let
`W_i(a)`, `P_j(y)` be non-negative integers with `P_j` supported on `R_j^A`,
`Σ_y P_j(y) = L`, and `W_i(a) = Σ_{y, y_k = a} P_j(y)` whenever `x_i` is the `k`-th
variable of `x̄_j` (Eq. (9)). If each `x_i ∈ A^L` contains every `a` exactly `W_i(a)` times,
then `X_i := f(x_i)` is a satisfying assignment of `X` in `𝔹`. -/
theorem rounding_satisfies {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A]
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) (X : Instance τ ar) {L : ℕ}
    (f : (Fin L → A) → B) (hf : IsPolymorphism 𝔸 𝔹 f) (hfs : IsSymmetric f)
    (W : Fin X.n → A → ℕ) (P : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℕ)
    (hPsupp : ∀ j y, y ∉ 𝔸.rel (X.sym j) → P j y = 0) (hPsum : ∀ j, ∑ y, P j y = L)
    (h9 : ∀ (j : Fin X.m) (k : Fin (ar (X.sym j))) (a : A),
      W (X.scope j k) a =
        ∑ y ∈ Finset.univ.filter (fun y : Fin (ar (X.sym j)) → A => y k = a), P j y)
    (x : Fin X.n → Fin L → A) (hx : ∀ i, HasCounts (x i) (W i)) :
    ∀ j : Fin X.m, (fun i => f (x i)) ∘ X.scope j ∈ 𝔹.rel (X.sym j) := by sorry

end PCSPBLPAff.Symmetric
