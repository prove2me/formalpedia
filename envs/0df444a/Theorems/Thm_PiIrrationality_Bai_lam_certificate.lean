-- Prove2me | Theorems.Thm_PiIrrationality_Bai_lam_certificate
-- name    : PiIrrationality.Bai.lam_certificate
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T19:57:02.293497+00:00
-- url     : https://prove2.me/theorems/173f152f-51d6-46a3-8f22-81782b36e342
-- title:
--   Certified interval table for Bai's deleted primes with $\lambda_{10^{16}}\ge 1202.5657733612916$
-- statement:
--   There is a list $L$ of rows $(A,B,f_1,f_2,f_3)$ such that every row is admissible (`okRow`: $A<B\le D\le 7430A$ with $D=7685213070$, the floors $\lfloor 1857u+\tfrac12\rfloor=f_1$, $\lfloor 3714u\rfloor=f_2$, $\lfloor 5570u\rfloor=f_3$ are constant on $[A/D,B/D)$, and Bai's inequality holds at $u=B/D$), consecutive rows are ordered (`chainOk`: $B_k\le A_{k+1}$), and
--   $$\lambda_{10^{16}}(L)=\sum_{m<10^{16}}\sum_{k}\Big(\frac{1}{m+A_k/D}-\frac{1}{m+B_k/D}\Big)\ge 1202.5657733612916 .$$
--
--   Role: the numerical half of Bai's prime saving $\omega=1202.56577336129180\ldots$ (Section 3); combined with `phi_lower_lam_of_MediumPNT` it gives $\Phi_n\ge e^{(1202.5657733612916-\delta)n}$.
-- source:
--   Y. Bai, The irrationality measure of π is at most 7.101862832357, arXiv:2609.11276 (v2, 11 Sep 2026), https://arxiv.org/abs/2609.11276, (2.14), (3.1) and Section 3 (prime saving omega)

import Definitions.Def_PiIrrationality_BaiForms

theorem PiIrrationality.Bai.lam_certificate :
    ∃ L : List (ℕ × ℕ × ℕ × ℕ × ℕ), L.all PiIrrationality.Bai.okRow = true ∧
      PiIrrationality.Bai.chainOk L = true ∧
      (1202.5657733612916 : ℝ) ≤ PiIrrationality.Bai.lam L (10 ^ 16) := by
  sorry
