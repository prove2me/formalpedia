-- Prove2me | Theorems.Thm_SaglamGV_exists_code_sharp
-- name    : SaglamGV.exists_code_sharp
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:49:29.579617+00:00
-- url     : https://prove2.me/theorems/df932517-2438-4cc1-b1ee-c4cca582ab00
-- title:
--   A distance-$d$ linear code with $|C|\ge\frac{1-\zeta}4\ln\frac{2^n}V\cdot\frac{2^n}V$
-- statement:
--   Fix $\varepsilon>0$ and $0<\zeta<1$. There are $L$ and $N_0$, depending only on $\varepsilon$ and $\zeta$, such that for all $n\ge N_0$ and all $w$ with $L\ln n\le w\le(1/2-\varepsilon)n$ there is a binary linear code $C\subseteq\mathbb F_2^n$ of distance at least $d=w+1$ with
--
--   $$
--   |C|\ge\frac{1-\zeta}4\,\ln\Big(\frac{2^n}V\Big)\,\frac{2^n}V .
--   $$
--
--   Since $\ln(2^n/V)=\Theta(n)$, this is $\Omega(n)$ times the Gilbert–Varshamov bound, with leading constant $1/4$ as $\zeta\to0$.
--
--   Differences from the source:
--   - encoding: ln n ≪ w and "for all sufficiently large n" → ∃ L, N₀ depending on ε, ζ only, for all n ≥ N₀ and L·ln n ≤ w ≤ (1/2 − ε)n; reason: equivalent to the sequential reading
--   - reading: "there is a code C" → a linear code (subspace of 𝔽₂ⁿ) with minimum distance at least d; reason: the sentence refers to the distance-d code constructed in the preceding sentence of p.5, which is the kernel of a parity-check matrix
--   - encoding: w = d − 1 → d = w + 1 with w : ℕ; reason: avoids natural-number subtraction
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), §3.3, p.5 (display |C| ≥ ((1 − ζ)/4) ln(2^n/V) (2^n/V))

import Mathlib
import Definitions.Def_SaglamGV_Code
import Definitions.Def_SaglamGV_Params

namespace SaglamGV

/-- The sharp size bound (M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript (held version, sha256 ac6f2bba…), §3.3, p.5: "Thus, for every fixed 0 < ζ < 1 and all sufficiently large
n, there is a code C satisfying |C| ≥ ((1 − ζ)/4) ln(2^n/V) (2^n/V)").

Fix $ε > 0$ and $0 < ζ < 1$. For all large $n$ and all $w$ with $\ln n ≪ w ≤ (1/2 − ε)n$ there is
a binary linear code of length $n$ and distance at least $d = w + 1$ with
$|C| ≥ \tfrac{1−ζ}{4}\ln(2^n/V)\cdot 2^n/V$.

**Formalization Note** "$\ln n ≪ w$" and "for all sufficiently large $n$" are $∃ L, N_0$ depending
on $ε, ζ$ only. The code is the linear code built on p.5 (a subspace of $𝔽_2^n$). -/
theorem exists_code_sharp (ε ζ : ℝ) (hε : 0 < ε) (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ L : ℝ, ∃ N₀ : ℕ, ∀ n w : ℕ, N₀ ≤ n → L * Real.log n ≤ w → (w : ℝ) ≤ (1 / 2 - ε) * n →
      ∃ C : Submodule (ZMod 2) (Fin n → ZMod 2), HasDistAtLeast C (w + 1) ∧
        (1 - ζ) / 4 * redund n (w + 1) * ((2 : ℝ) ^ n / (vol n (w + 1) : ℝ)) ≤ Nat.card C := by sorry

end SaglamGV
