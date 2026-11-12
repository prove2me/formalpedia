-- Prove2me | Theorems.Thm_Tao2022Collatz_characteristic_function_le_renewal_expectation
-- name    : Tao2022Collatz.characteristic_function_le_renewal_expectation
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-11T23:46:11.325197+00:00
-- url     : https://prove2.me/theorems/0292fe03-cc53-49ba-9215-db4a09383774
-- title:
--   Syracuse characteristic function bounded by the white-point renewal expectation (Tao, Lemma 7.2 and (7.5)-(7.6))
-- statement:
--   Let $n,K\in\mathbb{N}$, $\xi\in\mathbb{Z}$ and $0<\varepsilon\le 1$. For $\vec a=(a_1,\dots,a_n)\in[1,K]^n$ write $|\vec a|=a_1+\dots+a_n$, $a_{[1,i]}=a_1+\dots+a_i$, and let
--
--   $$\mathrm{Syr}(\vec a)=\Big(\sum_{j=0}^{n-1}3^{j}\,2^{|\vec a|-a_{[1,j+1]}}\Big)\cdot 2^{-|\vec a|}\in\mathbb{Z}/3^n\mathbb{Z}$$
--
--   be the $n$-Syracuse offset (Tao (1.11)-(1.12) for the truncated valuations), with representative $\mathrm{Syr}(\vec a)\in[0,3^n)$. Call $(J,L)$ *white* if the representative $t\in[0,3^n)$ of $\xi\,9^{J-1}2^{-(L-1)}$ satisfies $\varepsilon3^n<t<(1-\varepsilon)3^n$. If $V:\mathbb{N}^3\to\mathbb{R}$ satisfies $V(0,j,l)=1$ and
--
--   $$V(r+1,j,l)=\sum_{a_1,a_2\in[1,K]}2^{-(a_1+a_2)}\,e^{-\varepsilon^3\,\mathbf 1[a_1+a_2=3,\ (j+1,\,l+a_1+a_2)\ \text{white}]}\;V(r,j+1,l+a_1+a_2),$$
--
--   then
--
--   $$\Big|\sum_{\vec a\in[1,K]^n}2^{-|\vec a|}\,e^{-2\pi i\,\xi\,\mathrm{Syr}(\vec a)/3^n}\Big|\le V(\lfloor n/2\rfloor,0,0).$$
--
--   Role: this is the reduction of the Fourier decay of the Syracuse offsets to a renewal process: Tao's bound $|S_\chi(n)|\le\mathbb{E}\exp(-\varepsilon^3\#\{j\in[n/2]:b_j=3,(j,b_{[1,j]})\in W\})$, obtained from the pairing (7.5), the trivial bound (7.6) and the cancellation at white points (Lemma 7.2). Combined with the renewal estimate (Proposition 7.3) it yields Proposition 1.17.
--
--   **Formalization Note**: the expectation over the renewal process is written as any solution $V$ of its first-step recursion, so no probability space is needed; the geometric valuations are truncated to $[1,K]$ with weights $2^{-a_i}$ (the parent uses $K\ge n$), and the characteristic function is the corresponding finite sum. The bound holds for every $\varepsilon\in(0,1]$.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7, Section 7.1: (7.5), (7.6) and Lemma 7.2, the displayed bound |S_chi(n)| <= E exp(-eps^3 #{j in [n/2]: b_j = 3, (j, b_[1,j]) in W}) just before Proposition 7.3. https://arxiv.org/abs/1909.03562

import Mathlib

namespace Tao2022Collatz

theorem characteristic_function_le_renewal_expectation :
    ∀ n K : ℕ, ∀ ξ : ℤ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ V : ℕ → ℕ → ℕ → ℝ,
        (∀ j l : ℕ, V 0 j l = 1) →
        (∀ r j l : ℕ, V (r + 1) j l =
          ∑ u ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.Icc 1 K), ((1 : ℝ) / 2) ^ (∑ i, u i) *
            (if (∑ i, u i) = 3 ∧
                ε * 3 ^ n < ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) *
                  ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i - 1)).val : ℕ) : ℝ) ∧
                ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) *
                  ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i - 1)).val : ℕ) : ℝ) < (1 - ε) * 3 ^ n
              then Real.exp (-ε ^ 3) else 1) * V r (j + 1) (l + ∑ i, u i)) →
        ‖∑ w ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K), ((1 : ℂ) / 2) ^ (∑ i, w i) *
      Complex.exp (-(2 * Real.pi * Complex.I) * ξ *
        ((((∑ j ∈ Finset.range n, 3 ^ j * 2 ^ ((∑ i ∈ Finset.range n,
              (if h : i < n then w ⟨i, h⟩ else 1)) -
            ∑ i ∈ Finset.range (j + 1), (if h : i < n then w ⟨i, h⟩ else 1)) : ℕ) : ZMod (3 ^ n)) *
          ((2 : ZMod (3 ^ n))⁻¹) ^ (∑ i ∈ Finset.range n, (if h : i < n then w ⟨i, h⟩ else 1))).val : ℂ)
          / 3 ^ n)‖ ≤ V (n / 2) 0 0 := by sorry

end Tao2022Collatz
