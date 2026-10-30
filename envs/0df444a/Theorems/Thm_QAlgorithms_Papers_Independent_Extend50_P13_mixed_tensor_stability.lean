-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_mixed_tensor_stability
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.mixed_tensor_stability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:41:14.692009+00:00
-- url     : https://prove2.me/theorems/c523fcc5-1677-4556-a2c6-d9d7b3c9e106
-- title:
--   Theorem 12: mixed tensor stability
-- statement:
--   For $k=r+1\ge1$ and a partition $\lambda\vdash k$, let $T(\pi)$ permute tensor factors by $v_1\otimes\cdots\otimes v_k\mapsto v_{\pi^{-1}(1)}\otimes\cdots\otimes v_{\pi^{-1}(k)}$, and set $P_\lambda=\frac{\chi_\lambda(e)}{k!}\sum_{\pi\in S_k}\chi_\lambda(\pi^{-1})T(\pi)$ and $f_\lambda(X_1,\ldots,X_r)=\operatorname{tr}_{1\ldots r}[P_\lambda(X_1\otimes\cdots\otimes X_r\otimes I)]$. Here $\chi_\lambda$ is the character of the shape-labelled Specht representation, independently of $d$; shapes with more than $d$ rows are included. Let $n\ge0$, $k=r+1\ge1$, local dimensions $d_j\ge1$, and independently chosen partitions $\lambda_j\vdash k$ be given. For arbitrary globally positive semidefinite inputs $X_1,\ldots,X_r$ on $H=\bigotimes_{j=1}^n\mathbb C^{d_j}$, define $F=\bigotimes_j f_{\lambda_j}$ by vertically tensoring the projectors $P_{\lambda_j}$, regrouping them into $k$ copies of $H$, and contracting the first $r$ copies against $X_1,\ldots,X_r$. Then
--
--   $$F(X_1,\ldots,X_r)\ge0.$$
--
--   Inputs may be entangled across the parties. For $n=0$, $H=\mathbb C$ and the contraction multiplies the nonnegative scalar inputs. This is mixed tensor stability in the source's precise wiring.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 12, Theorem 12: mixed tensor stability

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Theorem 12, Eq.47 (PDF pp.11–12). Partitions/dimensions are independently
chosen, and inputs may be entangled across all parties. n=0 retains the scalar
empty tensor product and is not excluded. -/
theorem mixed_tensor_stability {n r : ℕ} (dims : Fin n → ℕ)
    (hdims : ∀ j, 0 < dims j)
    (lambda : Fin n → QAlgorithms.Schur.Partition (r+1) (r+1))
    (X : Fin r → (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ)) (hX : ∀ i, (X i).PosSemidef) :
    (mixedMap dims lambda X).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
