-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartV_corollary_5_3_1
-- name    : RamanujanLostNotebook.PartV.corollary_5_3_1
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-06T17:04:15.323387+00:00
-- url     : https://prove2.me/theorems/e10ca90e-64c8-4957-bd11-6c4c8ce3fd4f
-- title:
--   Equivalence of the first five mock theta conjectures
-- statement:
--   Let $M_1(q)=\chi_0(q)-2-3\Phi(q)+A(q)$, $M_2(q)=F_0(q)-1-\Phi(q)+q\,\psi(q^5)H(q^2)$, $M_3(q)=\phi_0(-q)+\Phi(q)-(q^5;q^5)_\infty G(q^2)H(q)/H(q^2)$, $M_4(q)=\psi_0(q)-\Phi(q^2)-q\,H(q)f(-q^9,-q)$, $M_5(q)=f_0(q)+2\Phi(q^2)-\varphi(-q^5)G(q)$, where $\chi_0(q)=\sum_{n\ge0}q^n/(q^{n+1};q)_n$; $\Phi(q)=-1+\sum_{n\ge0}q^{5n^2}/\big((q;q^5)_{n+1}(q^4;q^5)_n\big)$; $A(q)=G(q)^2(q^5;q^5)_\infty/H(q)$; $G(q)=\sum_{n\ge0}q^{n^2}/(q;q)_n$, $H(q)=\sum_{n\ge0}q^{n^2+n}/(q;q)_n$ (the Rogers-Ramanujan functions, series form); $F_0(q)=\sum_{n\ge0}q^{2n^2}/(q;q^2)_n$; $\varphi(q)=\sum_{n\in\mathbb Z}q^{n^2}$, $\psi(q)=\sum_{n\ge0}q^{n(n+1)/2}$, $f(a,b)=\sum_{n\in\mathbb Z}a^{n(n+1)/2}b^{n(n-1)/2}$; $\phi_0(q)=\sum_{n\ge0}(-q;q^2)_nq^{n^2}$; $\psi_0(q)=\sum_{n\ge1}(-q;q)_{n-1}q^{n(n+1)/2}$; $f_0(q)=\sum_{n\ge0}q^{n^2}/(-q;q)_n$. Then the five statements "$M_i(q)=0$ for all complex $q$ with $|q|<1$" ($1\le i\le5$) are pairwise equivalent.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 5, Corollary 5.3.1, p. 69.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_ch05_mtcM1
import Definitions.Def_RamanujanLostNotebook_PartV_ch05_mtcM2
import Definitions.Def_RamanujanLostNotebook_PartV_ch05_mtcM3
import Definitions.Def_RamanujanLostNotebook_PartV_ch05_mtcM4
import Definitions.Def_RamanujanLostNotebook_PartV_ch05_mtcM5

namespace RamanujanLostNotebook.PartV
theorem corollary_5_3_1 :
    List.TFAE [(∀ q : ℂ, ‖q‖ < 1 → mtcM1 q = 0),
      (∀ q : ℂ, ‖q‖ < 1 → mtcM2 q = 0),
      (∀ q : ℂ, ‖q‖ < 1 → mtcM3 q = 0),
      (∀ q : ℂ, ‖q‖ < 1 → mtcM4 q = 0),
      (∀ q : ℂ, ‖q‖ < 1 → mtcM5 q = 0)] := by sorry
end RamanujanLostNotebook.PartV
