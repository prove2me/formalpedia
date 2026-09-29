-- Prove2me | Theorems.Thm_ThornStringBits_trace_prod_cyclic
-- name    : ThornStringBits.trace_prod_cyclic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T01:33:21.486269+00:00
-- url     : https://prove2.me/theorems/b0b4527c-8236-4d1e-a9e4-10330cbe02e7
-- title:
--   Cyclic symmetry of the singlet trace $\mathrm{tr}\{\bar a(x_1)\cdots\bar a(x_M)\}$
-- statement:
--   Let $R$ be a commutative ring, let $N\ge 0$ and $M\ge 0$, and let $a_0,a_1,\dots,a_M$ be $M+1$ square matrices of size $N\times N$ with entries in $R$. Then
--   $$ \mathrm{tr}\,(a_0 a_1 \cdots a_M) = \mathrm{tr}\,(a_1 \cdots a_M a_0). $$
--
--   In Thorn's matrix formulation of string bits (p. 4) the singlet operator $\mathrm{tr}\{\bar a(x_1)\cdots\bar a(x_M)\}$ creates a discretized closed string; its invariance under cyclic relabelling of the bits is exactly the cyclic symmetry $\psi_M(x_1,\dots,x_M)=\psi_M(x_2,\dots,x_M,x_1)$ of the string wave function. The creation operators $\bar a_{k\ell}(x)$ commute among themselves, which is why the entries are taken in a commutative ring.
--
--   **Formalization Note** The product is the ordered product of the list $[a_0,\dots,a_M]$ and the rotated product is that of the list rotated left by one place.
-- source:
--   C. B. Thorn, *Reformulating String Theory with the 1/N Expansion*, arXiv:hep-th/9405069v1 (1994; talk at the First Int. A. D. Sakharov Conf., 1991), https://arxiv.org/abs/hep-th/9405069, pp. 4–5.

import Mathlib

open Real Matrix

namespace ThornStringBits

theorem trace_prod_cyclic {R : Type*} [CommRing R] {N M : ℕ}
    (a : Fin (M + 1) → Matrix (Fin N) (Fin N) R) :
    (List.ofFn a).prod.trace = ((List.ofFn a).rotate 1).prod.trace := by sorry

end ThornStringBits
