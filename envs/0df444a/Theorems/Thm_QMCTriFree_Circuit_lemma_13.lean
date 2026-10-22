-- Prove2me | Theorems.Thm_QMCTriFree_Circuit_lemma_13
-- name    : QMCTriFree.Circuit.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:47.147322+00:00
-- url     : https://prove2.me/theorems/f7667120-a0a0-438d-b627-88ea3c35a15e
-- title:
--   Lemma 13 — GP rounding of $\mathrm{Lasserre}_2$ gives $\mathbb E[E_{ij}]\ge f(x_{ij})$ (stated in expectation)
-- statement:
--   Let $M$ be feasible for $\mathrm{Lasserre}_2(H)$ with edge values $x_{ij}$, let $W$ be a Gram factorisation of its $\mathcal P^{(1)}_n$ block, and let $\vec v_k$ be the Bloch vectors produced by GP rounding from a Gaussian matrix $Z$. For distinct vertices $i\ne j$,
--   $$\mathbb E_Z\bigl[E_{ij}\bigr]\ \ge\ f(x_{ij})=\tfrac12-\tfrac4{3\pi}\Bigl(-\tfrac{1+2x_{ij}}3\Bigr)\,{}_2F_1\Bigl(\tfrac12,\tfrac12;\tfrac52;\Bigl(-\tfrac{1+2x_{ij}}3\Bigr)^2\Bigr),$$
--   where ${}_2F_1(a,b;c;z)=\sum_{n\ge0}\frac{(a)_n(b)_n}{(c)_n}\frac{z^n}{n!}$ and $(t)_n=t(t+1)\cdots(t+n-1)$.
--
--   This is the guarantee of the product-state stage relative to the relaxation.
--
--   **Formalization Note** The paper prints $E_{ij}\ge f(x_{ij})$ without an expectation; for a single draw it is false (e.g. a draw with $\vec v_i=\vec v_j$ gives $E_{ij}=0<f$), and its citation (Gharibian–Parekh, Briët–de Oliveira Filho–Vallentin) is an expectation bound, so the statement is posed in expectation. GP rounding is the Gaussian-projection reconstruction described in the definitions.
-- source:
--   King, An Improved Approximation Algorithm for Quantum Max-Cut on Triangle-Free Graphs, arXiv:2209.02589v3, p. 12, Lemma 13, eq. (12)

import Mathlib
import Definitions.Def_QMCTriFree_Circuit_Algorithm

set_option autoImplicit false

open QMCProduct.HalfApprox Matrix MeasureTheory ProbabilityTheory

namespace QMCTriFree.Circuit

/-- King, arXiv:2209.02589v3, p. 12, Lemma 13, eq. (12), stated in expectation over the GP
rounding: for a feasible `M`, a Gram factorisation `W` of its `P_n^(1)` block and `i ≠ j`,
`𝔼_Z[E_ij] ≥ f(x_ij)`. -/
theorem lemma_13 {n D : ℕ} (M : Matrix (P2 n) (P2 n) ℝ) (hM : IsFeasible M)
    (W : Fin n → Fin 3 → Fin D → ℝ) (hW : IsGramOfBlock M W) (i j : Fin n) (hij : i ≠ j) :
    fGP (xval M i j) ≤ ∫ Z, Eij (gpBloch W Z) i j ∂(gaussZ D) := by sorry

end QMCTriFree.Circuit
