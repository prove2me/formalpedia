-- Prove2me | Theorems.Thm_RamareAnalytic_exists_squarefree_totient_harmonic_coefficients
-- name    : RamareAnalytic.exists_squarefree_totient_harmonic_coefficients
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-19T20:45:48.025933+00:00
-- url     : https://prove2.me/theorems/a866384b-78aa-46c7-90df-9bbecf5707a5
-- title:
--   Multiplicative harmonic-convolution coefficients for the squarefree totient sum
-- statement:
--   Write $H_m=\sum_{j=1}^m 1/j$, with $H_0=0$, and let $\varphi$ be Euler's totient. There exists a multiplicative arithmetic function $h:\mathbb N\to\mathbb R$, vanishing at zero and satisfying $h(1)=1$, such that for every prime $p$,
--
--   $$h(p)=\frac1{p(p-1)},\qquad h(p^2)=-\frac1{p(p-1)},\qquad h(p^k)=0\quad(k\ge3),$$
--
--   and, for every natural cutoff $N$, including zero,
--
--   $$\sum_{n=1}^{N}\frac{\mathbf1_{\mathrm{Squarefree}(n)}}{\varphi(n)}
--   =\sum_{d=1}^{N}h(d)H_{\lfloor N/d\rfloor}.$$
--
--   Multiplicativity means $h(mn)=h(m)h(n)$ for coprime $m,n$. The same function witnesses every prime-power identity and every finite convolution identity. An explicit construction is $h(n)=(w*\mu)(n)/n$, where $w(n)=n\mathbf1_{\mathrm{Squarefree}(n)}/\varphi(n)$ and $*$ denotes Dirichlet convolution. This is the finite algebraic input to Ramaré's harmonic-convolution estimate; it does not assert absolute convergence, coefficient mass, logarithmic moments, or the large-range inequality.
-- source:
--   O. Ramaré, On Shnirelman's constant, Ann. Scuola Norm. Sup. Pisa 22 (1995), 645–706, printed pp.656–659, Lemma 3.2 and equations (3.7)–(3.8). https://www.numdam.org/item/ASNSP_1995_4_22_4_645_0/ . Formal reconstruction supporting the existing large-range target https://prove2.me/theorems/017351d0-907f-4262-b614-6850111f1ff0 . Prime-power factors and finite convolution follow equations (3.7)–(3.8), p.659. No novelty is claimed.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Totient
set_option autoImplicit false
open scoped BigOperators

theorem RamareAnalytic.exists_squarefree_totient_harmonic_coefficients :
    ∃ h : ArithmeticFunction ℝ, h.IsMultiplicative ∧
    (∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1)))) ∧
    (∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0) ∧
    (∀ N : ℕ,
      (∑ n ∈ Finset.Icc 1 N,
        if Squarefree n then (1 : ℝ) / Nat.totient n else 0) =
      ∑ d ∈ Finset.Icc 1 N, h d * (harmonic (N / d) : ℝ)) := by sorry
