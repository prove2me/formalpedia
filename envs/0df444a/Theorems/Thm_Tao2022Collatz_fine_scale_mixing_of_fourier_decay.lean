-- Prove2me | Theorems.Thm_Tao2022Collatz_fine_scale_mixing_of_fourier_decay
-- name    : Tao2022Collatz.fine_scale_mixing_of_fourier_decay
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-11T23:47:03.706164+00:00
-- url     : https://prove2.me/theorems/78d80f43-bb2f-44d7-a30d-4131c7985e20
-- title:
--   Fourier decay of Syracuse offsets implies fine-scale mixing (Tao, Prop 1.14 assuming Prop 1.17)
-- statement:
--   For $K\in\mathbb{N}$ and $\vec a\in[1,K]^n$ let $|\vec a|=a_1+\dots+a_n$, $a_{[1,i]}=a_1+\dots+a_i$ and let $\mathrm{Syr}(\vec a)=\big(\sum_{j=0}^{n-1}3^{j}2^{|\vec a|-a_{[1,j+1]}}\big)\,2^{-|\vec a|}\in\mathbb{Z}/3^n\mathbb{Z}$ be the $n$-Syracuse offset of the valuations $\vec a$ (Tao (1.11)-(1.12)). Suppose the truncated characteristic functions decay superpolynomially: for every $A>0$ there is $C>0$ with
--
--   $$\Big|\sum_{\vec a\in[1,K]^n}2^{-|\vec a|}e^{-2\pi i\,\xi\,\mathrm{Syr}(\vec a)/3^n}\Big|\le C\,n^{-A}\qquad(1\le n\le K,\ 3\nmid\xi).$$
--
--   Then the truncated Syracuse distributions mix at fine 3-adic scales: for every $A>0$ there is $C>0$ such that for $1\le m\le n\le K$ and $\mu(Y)=\sum_{\vec a\in[1,K]^n,\ \mathrm{Syr}(\vec a)=Y}2^{-|\vec a|}$ ($Y\in\mathbb{Z}/3^n\mathbb{Z}$),
--
--   $$\mathrm{Osc}_{m,n}(\mu)=\sum_{Y\in\mathbb{Z}/3^n\mathbb{Z}}\Big|\mu(Y)-3^{m-n}\sum_{Y'\equiv Y\ (3^m)}\mu(Y')\Big|\le C\,m^{-A}.$$
--
--   Role: this is Tao's Section 6, "Proposition 1.14 assuming Proposition 1.17": the Fourier decay bound (1.28) implies the fine-scale mixing (1.26)-(1.27) of the $n$-Syracuse offsets, which in turn yields the stabilisation of first passage (Proposition 1.11) used by the parent.
--
--   **Formalization Note**: the random valuations $a_i\sim\mathrm{Geom}(2)$ are truncated to $[1,K]$ with weights $2^{-a_i}$ (finite sums, no probability space); the parent uses $K\ge n$. The distribution $\mu$ is passed as any function satisfying its defining equation, and residues mod $3^m$ are compared through the canonical representatives $Y.\mathrm{val}$.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7, Section 6 (Reduction to Fourier decay bound): Proposition 1.14, (1.26)-(1.27), derived from Proposition 1.17, (1.28). https://arxiv.org/abs/1909.03562

import Mathlib

namespace Tao2022Collatz

theorem fine_scale_mixing_of_fourier_decay :
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ n K : ℕ, 1 ≤ n → n ≤ K → ∀ ξ : ℤ, ¬ (3 : ℤ) ∣ ξ →
    ‖∑ w ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K), ((1 : ℂ) / 2) ^ (∑ i, w i) *
      Complex.exp (-(2 * Real.pi * Complex.I) * ξ *
        ((((∑ j ∈ Finset.range n, 3 ^ j * 2 ^ ((∑ i ∈ Finset.range n,
              (if h : i < n then w ⟨i, h⟩ else 1)) -
            ∑ i ∈ Finset.range (j + 1), (if h : i < n then w ⟨i, h⟩ else 1)) : ℕ) : ZMod (3 ^ n)) *
          ((2 : ZMod (3 ^ n))⁻¹) ^ (∑ i ∈ Finset.range n, (if h : i < n then w ⟨i, h⟩ else 1))).val : ℂ)
          / 3 ^ n)‖ ≤ C * (n : ℝ) ^ (-A)) →
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ m n K : ℕ, 1 ≤ m → m ≤ n → n ≤ K →
    ∀ μ : ZMod (3 ^ n) → ℝ, (∀ Y : ZMod (3 ^ n), μ Y =
    ∑ w ∈ (Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K)).filter (fun w =>
      (((∑ j ∈ Finset.range n, 3 ^ j * 2 ^ ((∑ i ∈ Finset.range n,
              (if h : i < n then w ⟨i, h⟩ else 1)) -
            ∑ i ∈ Finset.range (j + 1), (if h : i < n then w ⟨i, h⟩ else 1)) : ℕ) : ZMod (3 ^ n)) *
          ((2 : ZMod (3 ^ n))⁻¹) ^ (∑ i ∈ Finset.range n, (if h : i < n then w ⟨i, h⟩ else 1))) = Y),
      ((1 : ℝ) / 2) ^ (∑ i, w i)) →
    ∑ Y : ZMod (3 ^ n), |μ Y - (3 : ℝ) ^ m / 3 ^ n *
      ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m), μ Y'|
      ≤ C * (m : ℝ) ^ (-A) := by sorry

end Tao2022Collatz
