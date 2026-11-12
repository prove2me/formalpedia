-- Prove2me | Theorems.Thm_Tao2022Collatz_first_passage_stabilisation_of_mixing
-- name    : Tao2022Collatz.first_passage_stabilisation_of_mixing
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-11T23:48:35.053607+00:00
-- url     : https://prove2.me/theorems/afc7b234-35d8-42b4-b0d0-034d6012cfad
-- title:
--   Fine-scale mixing implies stabilisation of first passage (Tao, Prop 1.11 assuming Prop 1.14)
-- statement:
--   Let $\mathrm{Syr}$ be the Syracuse map on odd integers ($\mathrm{Syr}(N)=(3N+1)/2^{\nu_2(3N+1)}$) and $\alpha=1.001$. For $y\ge 1$ let $\mathbf{N}_y$ be the log-uniform random odd integer in $[y,y^{\alpha}]$, i.e. $$\mathbb{P}(\mathbf{N}_y\in Q)=\frac{\sum_{N\in[\lceil y\rceil,\lfloor y^{\alpha}\rfloor],\ N\text{ odd},\ N\in Q}1/N}{\sum_{N\in[\lceil y\rceil,\lfloor y^{\alpha}\rfloor],\ N\text{ odd}}1/N}.$$ For $x>0$ let $T_x(N)$ be the first $k$ with $\mathrm{Syr}^k(N)\le x$ and $\mathrm{Pass}_x(N)=\mathrm{Syr}^{T_x(N)}(N)$. Assume moreover the three inputs of Section 5 proved as sibling lemmas: the harmonic-mass bound for one valuation block (Tao Lemma 5.3, `Tao2022Collatz.syracuse_block_class_sum_bound`), the valuation law of $\mathbf{N}_y$ with the geometric tail bounds and the projection identity (Tao Proposition 1.9, Lemma 2.2, (1.23), `Tao2022Collatz.valuation_law_and_tails`), and the Section 5 parameter estimates (`Tao2022Collatz.section5_parameter_estimates`); the formal statement takes each of them, verbatim, as a hypothesis. Assume also the fine-scale mixing of the $n$-Syracuse offsets (Tao, Proposition 1.14): for every $A>0$ there is $C>0$ such that for $1\le m\le n\le K$ and $\mu(Y)=\sum_{\vec a\in[1,K]^n,\ \mathrm{Syr}(\vec a)=Y}2^{-|\vec a|}$ ($Y\in\mathbb{Z}/3^n\mathbb{Z}$, $\mathrm{Syr}(\vec a)=\big(\sum_{j=0}^{n-1}3^{j}2^{|\vec a|-a_{[1,j+1]}}\big)2^{-|\vec a|}$), $$\sum_{Y\in\mathbb{Z}/3^n\mathbb{Z}}\Big|\mu(Y)-3^{m-n}\sum_{Y'\equiv Y\ (3^m)}\mu(Y')\Big|\le C\,m^{-A}.$$ Then (Tao, Proposition 1.11, (1.19)-(1.20)) there are $C,c>0$ and $x_0$ such that for all $x\ge x_0$, with $y=x^{\alpha}$ and $y=x^{\alpha^2}$, $$\mathbb{P}(T_x(\mathbf{N}_y)=\infty)\le C x^{-c}\quad\text{and}\quad \big|\mathbb{P}(\mathrm{Pass}_x(\mathbf{N}_{x^{\alpha}})\in E)-\mathbb{P}(\mathrm{Pass}_x(\mathbf{N}_{x^{\alpha^2}})\in E)\big|\le C\log^{-c}x$$ for every set $E$ (both events also require $T_x<\infty$).
--
--   Role: this is Tao's Section 5, "Proof of Proposition 1.11 assuming Proposition 1.14" (using Proposition 1.9 on the 2-adic distribution of the valuations); Proposition 1.11 is the stabilisation input of the parent's Section 3 telescoping argument.
--
--   **Formalization Note**: the law of $\mathbf{N}_y$ is passed as any function $P$ satisfying its defining equation; $\mu$ likewise; the Syracuse valuations are truncated to $[1,K]$ with weights $2^{-a_i}$ (finite sums). The passage events are written with the first index $k$ such that $\mathrm{Syr}^k(N)\le x$.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7, Section 5 (Proof of Proposition 1.11 assuming Proposition 1.14): Proposition 1.11, (1.19)-(1.20), with Proposition 1.9 and Proposition 5.2. https://arxiv.org/abs/1909.03562

import Mathlib
import Definitions.Def_syracuseStep

namespace Tao2022Collatz

theorem first_passage_stabilisation_of_mixing :
    (∀ (x : ℝ) (hx : 0 < x) (m k : ℕ) (hm : 1 ≤ m) (b : Fin m → ℕ) (S : Finset ℕ) (hsize : 4 * (3 : ℝ) ^ (k + m) * 2 ^ (b ⟨m - 1, by omega⟩) ≤ x) (hS : ∀ M ∈ S, (fun i : Fin m => (3 * syracuseStep^[(i : ℕ)] M + 1).factorization 2) = b ∧ (syracuseStep^[m] M : ℝ) ≤ x ∧ x < (syracuseStep^[m - 1] M : ℝ)) (hcong : ∀ M ∈ S, ∀ M' ∈ S, (3 : ℤ) ^ k ∣ (M' : ℤ) - M),
      (3 : ℝ) ^ k * ∑ M ∈ S, (1 : ℝ) / M ≤ ((1 : ℝ) / 2) ^ (∑ i, b i) * (2 + b ⟨m - 1, by omega⟩)) →
    ((∀ P : ℝ → (ℕ → Prop) → ℝ, (∀ (y : ℝ) (Q : ℕ → Prop), P y Q =
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
          μ₁ Z * ∑ v ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 K), ((1 : ℝ) / 2) ^ (∑ i, v i))) →
    (∀ (pn0 : ℝ → ℕ) (pD pL pW pWt peps : ℝ → ℝ) (pm0 pK pDm : ℝ → ℕ),
    (∀ x, pn0 x = ⌊Real.log x / (10 * Real.log 2)⌋₊) →
    (∀ x, pD x = 2 * Real.log x ^ ((3 : ℝ) / 5)) →
    (∀ x, pL x = Real.log x ^ ((1 : ℝ) / 5)) →
    (∀ x, pW x = 2 * ((2 * pD x + 1) * Real.log 2) + Real.log (4 / 3)) →
    (∀ x, pWt x = pW x + pD x * Real.log 2 + Real.log 2) →
    (∀ x, peps x = 2 * (3 / 2 : ℝ) ^ (pn0 x) / x) →
    (∀ x, pm0 x = ⌈(pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1) / Real.log (4 / 3)⌉₊) →
    (∀ x, pK x = ⌈2 * (pn0 x : ℝ) + pD x⌉₊) →
    (∀ x, pDm x = ⌈4 * pD x + 2⌉₊) →
    (∀ (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5),
      1 ≤ x ∧ 0 ≤ pD x ∧ pD x = 2 * u ^ 3 ∧ pL x = u ∧ 1000000 * u ^ 3 ≤ Real.log x ∧
    u ≤ u ^ 3 ∧ 6.931 * (pn0 x : ℝ) ≤ Real.log x ∧ Real.log x ≤ 6.932 * ((pn0 x : ℝ) + 1) ∧
    0 ≤ pW x ∧ pW x ≤ 6 * u ^ 3 ∧ 0 ≤ pWt x ∧ pWt x ≤ 8 * u ^ 3 ∧
    pW x + 2 * ((2 * pD x + 1) * Real.log 2) + 1 ≤ pm0 x * Real.log (4 / 3) ∧
    (pm0 x : ℝ) * Real.log (4 / 3) ≤ 13 * u ^ 3 ∧ (pm0 x : ℝ) ≤ 52 * u ^ 3 ∧ 1 ≤ pm0 x ∧
    u ≤ (pm0 x : ℝ) ∧ 2 * (pn0 x : ℝ) + pD x ≤ pK x ∧
    4 * pD x + 2 ≤ pDm x ∧ (pDm x : ℝ) ≤ 8 * u ^ 3 + 3) ∧
    (∀ (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5),
      0 ≤ peps x ∧ peps x * u ≤ 1 ∧ peps x ≤ 1 ∧ 2 * (3 / 2 : ℝ) ^ (pn0 x) ≤ peps x * x ∧
    4 * (3 : ℝ) ^ (pn0 x + pm0 x) * 2 ^ (pDm x) ≤ x ∧
    1 * (Real.sqrt (pn0 x * pL x) + pL x) ≤ pD x ∧ pm0 x ≤ pn0 x) ∧
    (∀ (x u a : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) (ha1 : 1001 / 1000 ≤ a) (ha2 : a ≤ 1002001 / 1000000),
      16 ≤ x ^ a ∧ x ≤ x ^ a ∧ x ^ a + 1 ≤ (x ^ a) ^ ((1001 : ℝ) / 1000) ∧ (4 : ℝ) ^ (pn0 x) ≤ x ^ a ∧
    ((1001 : ℝ) / 1000) * Real.log (x ^ a) + pn0 x * Real.log (3 / 4) + (2 * pD x + 1) * Real.log 2 ≤ Real.log x ∧
    (pm0 x + 1) * Real.log (4 / 3) + (2 * pD x + 1) * Real.log 2 ≤ Real.log (x ^ a) - Real.log x ∧
    2 * pm0 x * Real.log (4 / 3) ≤ Real.log (x ^ a) - Real.log x + pWt x ∧
    2 * pWt x ≤ Real.log (x ^ a) - Real.log x + pWt x ∧
    Real.log (x ^ a) - Real.log x + pWt x ≤ ((1001 : ℝ) / 1000) * Real.log (x ^ a) - Real.log x - pWt x ∧
    ((1001 : ℝ) / 1000) * Real.log (x ^ a) - Real.log x - pWt x ≤ pn0 x * Real.log (4 / 3) ∧
    4 ≤ (((1001 : ℝ) / 1000) - 1) * Real.log (x ^ a)) ∧
    (∀ (ε eb Wt Λ ly h u : ℝ) (hu : 1000 ≤ u) (hly : u ^ 5 / 1000 ≤ ly) (hε0 : 0 ≤ ε) (hεu : ε * u ≤ 1) (hε1 : ε ≤ 1) (heb : 0 ≤ eb) (hWt0 : 0 ≤ Wt) (hWt : Wt ≤ 8 * u ^ 3) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ 4) (ha : 1 / 4 ≤ h) (hb : h ≤ 1 / 3),
      (4 * (ε * (ly / h + 1) * 4 + (ly / h + 1) * eb + (1 + ε) * (2 * (2 * Wt / h + 1)) * 4) / ly +
      Λ * (4 * ((2 * Wt / h + 1) + 2 / h) / ly)) ≤ 5500 / u + 20 * eb) ∧
    (∀ (x u Cosc : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5) (hCosc : 0 ≤ Cosc),
      4 * ((pn0 x : ℝ) * (1 / 2) ^ (pK x) + Cosc * (pm0 x : ℝ) ^ (-(1 : ℝ)) +
      2 * pn0 x * Real.exp (-(1 * pL x) / 24)) ≤ 4 * (1 + Cosc + 2 * 137594142720) / u) ∧
    (∀ (x u : ℝ) (hu : 1000 ≤ u) (hx0 : 0 < x) (hx : Real.log x = u ^ 5),
      8 * x ^ (-(1 / 20000 : ℝ)) + 2 * Real.log x * Real.exp (-(Real.log x ^ ((1 : ℝ) / 5)) / 24) ≤
      (8 + 2 * 137594142720) / u)) →
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ m n K : ℕ, 1 ≤ m → m ≤ n → n ≤ K →
    ∀ μ : ZMod (3 ^ n) → ℝ, (∀ Y : ZMod (3 ^ n), μ Y =
    ∑ w ∈ (Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 K)).filter (fun w =>
      (((∑ j ∈ Finset.range n, 3 ^ j * 2 ^ ((∑ i ∈ Finset.range n,
              (if h : i < n then w ⟨i, h⟩ else 1)) -
            ∑ i ∈ Finset.range (j + 1), (if h : i < n then w ⟨i, h⟩ else 1)) : ℕ) : ZMod (3 ^ n)) *
          ((2 : ZMod (3 ^ n))⁻¹) ^ (∑ i ∈ Finset.range n, (if h : i < n then w ⟨i, h⟩ else 1))) = Y),
      ((1 : ℝ) / 2) ^ (∑ i, w i)) →
    ∑ Y : ZMod (3 ^ n), |μ Y - (3 : ℝ) ^ m / 3 ^ n *
      ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) => Y'.val % 3 ^ m = Y.val % 3 ^ m), μ Y'|
      ≤ C * (m : ℝ) ^ (-A)) →
  ∀ P : ℝ → (ℕ → Prop) → ℝ, (∀ (y : ℝ) (Q : ℕ → Prop), P y Q =
    (∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd,
        Set.indicator {N | Q N} (fun N : ℕ => (1 : ℝ) / N) N) /
      ∑ N ∈ (Finset.Icc ⌈y⌉₊ ⌊y ^ ((1001 : ℝ) / 1000)⌋₊).filter Odd, (1 : ℝ) / N) →
  ∃ C c x0 : ℝ, 0 < C ∧ 0 < c ∧ ∀ x : ℝ, x0 ≤ x →
    P (x ^ ((1001 : ℝ) / 1000)) (fun N => ¬ ∃ k, (syracuseStep^[k] N : ℝ) ≤ x) ≤ C * x ^ (-c) ∧
    P (x ^ (((1001 : ℝ) / 1000) ^ 2)) (fun N => ¬ ∃ k, (syracuseStep^[k] N : ℝ) ≤ x) ≤ C * x ^ (-c) ∧
    ∀ E : ℕ → Prop,
      |P (x ^ ((1001 : ℝ) / 1000)) (fun N => ∃ k, (syracuseStep^[k] N : ℝ) ≤ x ∧
          (∀ j < k, x < (syracuseStep^[j] N : ℝ)) ∧ E (syracuseStep^[k] N)) -
        P (x ^ (((1001 : ℝ) / 1000) ^ 2)) (fun N => ∃ k, (syracuseStep^[k] N : ℝ) ≤ x ∧
          (∀ j < k, x < (syracuseStep^[j] N : ℝ)) ∧ E (syracuseStep^[k] N))| ≤
        C * Real.log x ^ (-c) := by sorry

end Tao2022Collatz
