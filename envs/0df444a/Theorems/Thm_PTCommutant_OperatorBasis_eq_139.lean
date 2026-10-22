-- Prove2me | Theorems.Thm_PTCommutant_OperatorBasis_eq_139
-- name    : PTCommutant.OperatorBasis.eq_139
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:24.945836+00:00
-- url     : https://prove2.me/theorems/f71873aa-886c-4db7-8145-640032681a21
-- title:
--   Eq. (139), p. 25 — orthogonality relation (1/|G|) Σ_g φ^α_{ij}(g) φ^β_{kp}(g⁻¹) = (1/d_α) δ^{αβ} δ_{ip} δ_{jk} for G = S(n−2)
-- statement:
--   Let $\varphi^\alpha$, $\alpha$ in a finite label set, be matrix representations of $G=S(n-2)$ of dimensions $d_\alpha\ge1$ by real orthogonal matrices, irreducible over $\mathbb C$ and pairwise inequivalent over $\mathbb C$. Then for all labels $\alpha,\beta$ and indices $i,j\le d_\alpha$, $k,p\le d_\beta$:
--   $$\frac1{(n-2)!}\sum_{g\in S(n-2)}\varphi^\alpha_{ij}(g)\,\varphi^\beta_{kp}(g^{-1})=\frac1{d_\alpha}\,\delta^{\alpha\beta}\,\delta_{ip}\,\delta_{jk}.$$
--   Stated as two clauses: for $\alpha=\beta$ the left side is $1/d_\alpha$ when $i=p$ and $j=k$ and $0$ otherwise; for $\alpha\neq\beta$ the sum is $0$.
--
--   This is the fundamental orthogonality relation for irreducible matrix representations; the paper uses it to derive the matrix-unit law of the $E^\alpha_{ij}$ and, through it, the group-algebra formulas (86) behind Theorem 9.
--
--   **Formalization Note.** $n=m+2$, so $|G|=(n-2)!=m!$. The printed (139) has two slips: the sum runs over $h\in G$ with summand in $g$, and the normalization is written $1/n!$ where Notation 32 sets $|G|=n$; the statement is the intended relation with $1/|G|$ and the sum over $g\in G$. The entries are real.
-- source:
--   Studziński, Horodecki, Mozrzymas, Commutant structuture of U⊗(n−1)⊗U* transformations, arXiv:1305.6183v2, p. 25, eq. (139) (proof of Theorem 34); Notation 32 p. 24

import Mathlib
import Definitions.Def_PTCommutant_OperatorBasis_Model

namespace PTCommutant.OperatorBasis

theorem eq_139 {m : ℕ} (F : IrrepFamily m) :
    (∀ (α : F.ι) (i j k p : Fin (F.dim α)),
      (1 / (m.factorial : ℝ)) * ∑ σ : Equiv.Perm (Fin m), F.rep α σ i j * F.rep α (σ⁻¹) k p =
        if i = p ∧ j = k then 1 / (F.dim α : ℝ) else 0) ∧
    (∀ (α β : F.ι), α ≠ β → ∀ (i j : Fin (F.dim α)) (k p : Fin (F.dim β)),
      ∑ σ : Equiv.Perm (Fin m), F.rep α σ i j * F.rep β (σ⁻¹) k p = 0) := by sorry

end PTCommutant.OperatorBasis
