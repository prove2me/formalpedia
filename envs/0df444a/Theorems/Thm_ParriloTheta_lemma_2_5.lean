-- Prove2me | Theorems.Thm_ParriloTheta_lemma_2_5
-- name    : ParriloTheta.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:10.115215+00:00
-- url     : https://prove2.me/theorems/3e465c8b-09fd-4841-ae8b-dcd416bd5dfa
-- title:
--   Lemma 2.5 — zeros of $x^TMx$ and $\mathcal K^{(1)}$-certificates (corrected: $P(i)_{jk}$ in (ii))
-- statement:
--   Let $M\in\mathcal K^{(1)}_n$, let $P(1),\dots,P(n)$ be a $\mathcal K^{(1)}$-certificate of $M$, and let $x\in\mathbb R^n_+$ satisfy $x^TMx=0$. Then:
--   1. if $x_i>0$ then $P(i)x=0$;
--   2. if $x_i,x_j,x_k>0$ then
--   $$
--   M_{ij}+M_{jk}+M_{ik}=P(i)_{jk}+P(j)_{ik}+P(k)_{ij}.
--   $$
--
--   These kernel properties are the basic tool of §6: every zero of the quadratic form constrains every certificate.
--
--   Differences from the source:
--   - correction: (ii) … = P(i)_ij + P(j)_ik + P(k)_ij → (ii) … = P(i)_jk + P(j)_ik + P(k)_ij; reason: the printed first term is false: for the Horn matrix H = M_{C5} with its certificate (2.7), x = (1,1,0,2,0) (a zero of xᵀHx) and (i,j,k) = (1,2,4), H₁₂ + H₂₄ + H₁₄ = −1 but P(1)₁₂ + P(2)₁₄ + P(4)₁₂ = 1; the corrected term is the x_i x_j x_k coefficient of (2.6), as used in Lemma 6.4
--   - encoding: matrices indexed by [n]; P(i)_jk → finite type ι; P i j k; reason: Lean convention
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, Lemma 2.5, p.6

import Mathlib
import Definitions.Def_ParriloTheta_InK
import Definitions.Def_ParriloTheta_IsK1Cert

open Matrix

namespace ParriloTheta

/-- **Lemma 2.5: kernel of a `K^(1)`-certificate at a zero (corrected (ii)).**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, Lemma 2.5, p.6:
"Let M ∈ K(1)_n and let P(1), . . . , P(n) be a K(1)-certificate of M. Let x ∈ R^n_+ such that
xᵀMx = 0. Then the following holds: (i) If x_i > 0 then P(i)x = 0. (ii) If x_i, x_j, x_k > 0
then M_ij + M_jk + M_ik = P(i)_ij + P(j)_ik + P(k)_ij."

**Correction.** In (ii) the first term `P(i)_ij` is a misprint for `P(i)_jk` (the coefficient
of `x_i x_j x_k` in (2.6), as used in Lemma 6.4). The printed form is false: for the Horn matrix
`H = M_{C5}` with the certificate (2.7), `x = (1,1,0,2,0)` and `(i,j,k) = (1,2,4)`,
`H_12 + H_24 + H_14 = −1` but `P(1)_12 + P(2)_14 + P(4)_12 = 1`.

**Formalization Note.** `P(i)_jk` is `P i j k`; `P(i)x` is `(P i).mulVec x`; `xᵀMx` is
`x ⬝ᵥ M *ᵥ x`. -/
theorem lemma_2_5 {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (P : ι → Matrix ι ι ℝ)
    (hM : InK 1 M) (hP : IsK1Cert M P) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hxM : x ⬝ᵥ (M *ᵥ x) = 0) :
    (∀ i, 0 < x i → (P i) *ᵥ x = 0) ∧
    (∀ i j k, 0 < x i → 0 < x j → 0 < x k →
      M i j + M j k + M i k = P i j k + P j i k + P k i j) := by sorry

end ParriloTheta
