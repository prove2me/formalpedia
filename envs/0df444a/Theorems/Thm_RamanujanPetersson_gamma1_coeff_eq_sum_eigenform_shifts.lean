-- Prove2me | Theorems.Thm_RamanujanPetersson_gamma1_coeff_eq_sum_eigenform_shifts
-- name    : RamanujanPetersson.gamma1_coeff_eq_sum_eigenform_shifts
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-13T01:30:17.248951+00:00
-- url     : https://prove2.me/theorems/fc6bcdec-3c35-4742-a317-508c8ec1163f
-- title:
--   Atkin–Lehner–Li: coefficients of a cusp form on $\Gamma_1(M)$ are a combination of shifted newform coefficients
-- statement:
--   Let $M\ge1$, $k\ge1$ and $g=\sum_n a(n)q^n\in S_k(\Gamma_1(M))$. Then there are finitely many data $(c_i,d_i,L_i,\chi_i,F_i)$, with $c_i\in\mathbb C$, $d_i,L_i\ge1$, $d_iL_i\mid M$, $\chi_i$ a Dirichlet character mod $L_i$ and $F_i=\sum_n b_i(n)q^n\in S_k(\Gamma_1(L_i))$, such that
--
--   $$a(n)=\sum_i c_i\, b_i(n/d_i)\qquad(n\ge0),$$
--
--   where $b_i(n/d_i)=0$ when $d_i\nmid n$, and each $F_i$ satisfies: $F_i|_k\gamma=\chi_i(d)F_i$ for $\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\Gamma_0(L_i)$; $b_i(1)=1$; for every prime $p$ and every $n\ge0$
--
--   $$b_i(pn)=b_i(p)b_i(n)-\mathbf 1_{p\nmid L_i}\,\chi_i(p)p^{k-1}\,b_i(n/p);$$
--
--   and $|b_i(p)|\le p^{(k-1)/2}$ for every prime $p\mid L_i$.
--
--   Role: the $F_i$ are the newforms of level $L_i\mid M$ and $g$ is a combination of the old forms $F_i(d_i\tau)$; this child reduces Ramanujan–Petersson on $\Gamma_1(M)$ to normalized eigenforms. The bad-prime bound is Li's computation of $a_p$ for $p\mid L$.
--
--   **Formalization Note**: everything is stated through Mathlib `qExpansion` coefficients with width $1$; the eigenform conditions are written out as coefficient identities.
-- source:
--   F. Diamond, J. Shurman, A First Course in Modular Forms (GTM 228), Springer 2005, https://doi.org/10.1007/978-0-387-27226-9, Theorems 5.8.2 and 5.8.3 (newform/oldform decomposition of $S_k(\Gamma_1(N))$) and Proposition 5.8.5; W.-C. W. Li, Newforms and functional equations, Math. Ann. 212 (1975), 285–315, https://doi.org/10.1007/BF01344466, Theorems 3 and 5; T. Miyake, Modular Forms, Springer, https://doi.org/10.1007/3-540-29593-3, Theorem 4.6.17 (eigenvalues at $p\mid N$)

import Mathlib
open UpperHalfPlane Filter Asymptotics MatrixGroups ModularForm

namespace RamanujanPetersson

theorem gamma1_coeff_eq_sum_eigenform_shifts (M : ℕ) (hM : 0 < M) (k : ℤ) (hk : 1 ≤ k)
    (g : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ (r : ℕ) (c : Fin r → ℂ) (d L : Fin r → ℕ) (χ : (i : Fin r) → DirichletCharacter ℂ (L i))
      (F : (i : Fin r) → CuspForm ((CongruenceSubgroup.Gamma1 (L i) : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ)) k),
      (∀ i, 0 < d i ∧ 0 < L i ∧ d i * L i ∣ M) ∧
      (∀ i, ∀ γ ∈ CongruenceSubgroup.Gamma0 (L i),
        (⇑(F i) ∣[k] γ) = χ i ((γ 1 1 : ℤ) : ZMod (L i)) • ⇑(F i)) ∧
      (∀ i, (qExpansion 1 (F i)).coeff 1 = 1) ∧
      (∀ i, ∀ p n : ℕ, p.Prime →
        (qExpansion 1 (F i)).coeff (p * n) =
          (qExpansion 1 (F i)).coeff p * (qExpansion 1 (F i)).coeff n -
            (if p ∣ L i then 0 else
              χ i (p : ZMod (L i)) * (p : ℂ) ^ (k - 1) *
                (if p ∣ n then (qExpansion 1 (F i)).coeff (n / p) else 0))) ∧
      (∀ i, ∀ p : ℕ, p.Prime → p ∣ L i →
        ‖(qExpansion 1 (F i)).coeff p‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2)) ∧
      ∀ n : ℕ, (qExpansion 1 g).coeff n =
        ∑ i, c i * (if d i ∣ n then (qExpansion 1 (F i)).coeff (n / d i) else 0) := by sorry

end RamanujanPetersson
