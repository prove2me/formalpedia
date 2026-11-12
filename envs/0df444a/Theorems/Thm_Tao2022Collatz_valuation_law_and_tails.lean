-- Prove2me | Theorems.Thm_Tao2022Collatz_valuation_law_and_tails
-- name    : Tao2022Collatz.valuation_law_and_tails
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-11T23:47:58.731566+00:00
-- url     : https://prove2.me/theorems/8897dbfc-ffff-4e0d-8db8-b4aff589986e
-- title:
--   Valuation law of $\mathbf{N}_y$, geometric tail bounds and projection of Syracuse offsets (Tao Prop. 1.9, Lemma 2.2, (1.23))
-- statement:
--   Let $\alpha=1.001$ and let $\mathbf{N}_y$ be the log-uniform random odd integer in $[y,y^{\alpha}]$, its law given by any $P$ with $P(y,Q)=\big(\sum_{N\in[\lceil y\rceil,\lfloor y^\alpha\rfloor]\text{ odd},\,Q(N)}1/N\big)/Z_y$, $Z_y=\sum_{N\in[\lceil y\rceil,\lfloor y^\alpha\rfloor]\text{ odd}}1/N$. Then:
--
--   (i) (Proposition 1.9, explicit) if $n\ge 1$, $2\cdot 2^{3n}\le\lceil y\rceil$ and $Z_y>0$, then for every set $E$ of valuation vectors,
--   $$\Big|\mathbb{P}\big(\vec a^{(n)}(\mathbf{N}_y)\in E\big)-\sum_{v\in[1,3n]^n,\ |v|<3n,\ v\in E}2^{-|v|}\Big|\le\Big(\frac{2\cdot 2^{6n+1}}{\lceil y\rceil Z_y}+2\Big)\Big(\frac89\Big)^n;$$
--   (ii) (Lemma 2.2, lower tail) for $n\ge1$ and all $K$: $\sum_{w\in[1,K]^n,\ 10|w|<19n}2^{-|w|}\le e^{-n/2400}$;
--   (iii) (Lemma 2.2, deviation) for $C\ge1$, $L\ge0$: $\sum_{w\in[1,K]^n}2^{-|w|}\,\mathbf{1}\big[\exists j\in[1,n]:\ |w_1+\dots+w_j-2j|>C(\sqrt{jL}+L)\big]\le 2n\,e^{-CL/24}$;
--   (iv) ((1.23), projection) with $\mu_n(Y)=\sum_{w\in[1,K]^n,\ \mathrm{Syr}(w)=Y}2^{-|w|}$ on $\mathbb{Z}/3^n\mathbb{Z}$, for all $m,k$ and $Z\in\mathbb{Z}/3^m\mathbb{Z}$: $\sum_{Y\equiv Z\,(3^m)}\mu_{m+k}(Y)=\mu_m(Z)\sum_{v\in[1,K]^k}2^{-|v|}$.
--
--   Role: these are the probabilistic inputs of Tao's Section 5 (Proposition 1.9 on the 2-adic distribution of the valuations of $\mathbf{N}_y$, the Chernoff bounds of Lemma 2.2 for geometric sums, and the compatibility (1.23) of the offset distributions under reduction), packaged for the proof of Proposition 1.11.
--
--   **Formalization Note**: the geometric law is truncated to $[1,K]$ with weights $2^{-a_i}$ (finite sums); in (i) the comparison measure is the $\mathrm{Geom}(2)$ law restricted to $|v|<3n$, as in Tao's proof (Lemma 4.1); $\mathrm{Syr}(w)=\big(\sum_{j<n}3^j2^{|w|-w_{[1,j+1]}}\big)2^{-|w|}$ in $\mathbb{Z}/3^n\mathbb{Z}$.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7, Proposition 1.9 (proved in Section 4 via Lemma 4.1), Lemma 2.2 (Chernoff type bound) and (1.23); used in Section 5 (5.4)-(5.5), (5.12). https://arxiv.org/abs/1909.03562

import Mathlib
import Definitions.Def_syracuseStep

namespace Tao2022Collatz

theorem valuation_law_and_tails :
    (∀ P : ℝ → (ℕ → Prop) → ℝ, (∀ (y : ℝ) (Q : ℕ → Prop), P y Q =
      (∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd,
          Set.indicator {N | Q N} (fun N : ℕ => (1 : ℝ) / N) N) /
        ∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd, (1 : ℝ) / N) →
      ∀ (y : ℝ) (n : ℕ), 1 ≤ n → 2 * 2 ^ (3 * n) ≤ ⌈y⌉₊ →
      0 < ∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd, (1 : ℝ) / N →
      ∀ (E : (Fin n → ℕ) → Prop) [DecidablePred E],
      |P y (fun N => E (fun i => (3 * syracuseStep^[(i : ℕ)] N + 1).factorization 2)) -
        ∑ v ∈ ((Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 (3 * n))).filter
            (fun v => ∑ i, v i < 3 * n)).filter E, ((1 : ℝ) / 2) ^ (∑ i, v i)| ≤
        (2 * (2 ^ (6 * n + 1) / ((⌈y⌉₊ : ℝ) *
          ∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd, (1 : ℝ) / N)) + 2) *
          (8 / 9) ^ n) ∧
    (∀ (n K : ℕ), 1 ≤ n →
      ∑ w ∈ (Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K)).filter
          (fun w => 10 * (∑ i, w i) < 19 * n), ((1 : ℝ) / 2) ^ (∑ i, w i) ≤
        Real.exp (-(n : ℝ) / 2400)) ∧
    (∀ (n K : ℕ) (C L : ℝ), 1 ≤ C → 0 ≤ L →
      ∑ w ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K),
        Set.indicator {w : Fin n → ℕ | ∃ j ∈ Finset.Icc 1 n, C * (Real.sqrt (j * L) + L) <
            |((∑ i ∈ Finset.range j, (if h : i < n then w ⟨i, h⟩ else 1) : ℕ) : ℝ) - 2 * j|}
          (fun w => ((1 : ℝ) / 2) ^ (∑ i, w i)) w ≤ 2 * n * Real.exp (-(C * L) / 24)) ∧
    (∀ (m k K : ℕ) (μ₁ : ZMod (3 ^ m) → ℝ) (μ₂ : ZMod (3 ^ (m + k)) → ℝ),
      (∀ Y : ZMod (3 ^ m), μ₁ Y =
        ∑ w ∈ (Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 K)).filter (fun w =>
          (((∑ j ∈ Finset.range m, 3 ^ j * 2 ^ ((∑ i ∈ Finset.range m,
                  (if h : i < m then w ⟨i, h⟩ else 1)) -
                ∑ i ∈ Finset.range (j + 1), (if h : i < m then w ⟨i, h⟩ else 1)) : ℕ) : ZMod (3 ^ m)) *
              ((2 : ZMod (3 ^ m))⁻¹) ^ (∑ i ∈ Finset.range m, (if h : i < m then w ⟨i, h⟩ else 1))) = Y),
          ((1 : ℝ) / 2) ^ (∑ i, w i)) →
      (∀ Y : ZMod (3 ^ (m + k)), μ₂ Y =
        ∑ w ∈ (Fintype.piFinset (fun _ : Fin (m + k) => Finset.Icc 1 K)).filter (fun w =>
          (((∑ j ∈ Finset.range (m + k), 3 ^ j * 2 ^ ((∑ i ∈ Finset.range (m + k),
                  (if h : i < m + k then w ⟨i, h⟩ else 1)) -
                ∑ i ∈ Finset.range (j + 1), (if h : i < m + k then w ⟨i, h⟩ else 1)) : ℕ) :
                  ZMod (3 ^ (m + k))) *
              ((2 : ZMod (3 ^ (m + k)))⁻¹) ^
                (∑ i ∈ Finset.range (m + k), (if h : i < m + k then w ⟨i, h⟩ else 1))) = Y),
          ((1 : ℝ) / 2) ^ (∑ i, w i)) →
      ∀ Z : ZMod (3 ^ m),
        ∑ Y ∈ Finset.univ.filter (fun Y : ZMod (3 ^ (m + k)) => ((Y.val : ℕ) : ZMod (3 ^ m)) = Z), μ₂ Y =
          μ₁ Z * ∑ v ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 K), ((1 : ℝ) / 2) ^ (∑ i, v i)) := by sorry

end Tao2022Collatz
