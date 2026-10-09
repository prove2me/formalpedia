-- Prove2me | Theorems.Thm_SWPort_Davenport_perron_of_region_bound
-- name    : SWPort.Davenport.perron_of_region_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T19:22:34.295545+00:00
-- url     : https://prove2.me/theorems/3cce0198-9332-42a6-a2c0-c2adea90714a
-- title:
--   Quantitative Perron theorem: partial sums of a Dirichlet series from an $O(\log^2)$ bound on its analytic continuation in a zero-free region (ported to Mathlib 0df444a)
-- statement:
--   **Partial sums of a Dirichlet series from a zero-free region, with de la Vallée Poussin error.** Fix a region constant $c>0$ and a constant $C_0>0$. There are constants $c_1,c_2,C>0$, depending only on $c$ and $C_0$, such that the following holds for every parameter $q\ge1$ (a natural number, playing the role of the modulus in the shape of the region), every sequence of complex coefficients $a(n)$, every function $G:\mathbb{C}\to\mathbb{C}$, every finite set $P\subset\mathbb{C}$ of "poles" and every assignment $r:P\to\mathbb{C}$ of "residues", provided that:
--
--   1. $|a(n)|\le\Lambda(n)$ for all $n$ ($\Lambda$ the von Mangoldt function);
--   2. $G(s)=\sum_{n\ge1}a(n)n^{-s}$ whenever $\operatorname{Re}s>1$;
--   3. $G$ is analytic (in a neighbourhood of each point) on the set $\{s=\sigma+it:\ \sigma\ge1-c/\log(q(|t|+2)),\ \sigma\ge3/4\}\setminus P$;
--   4. every $p\in P$ satisfies $1/2\le\operatorname{Re}p\le1$;
--   5. $\sum_{p\in P}|r(p)|\le C_0\log(2q)$;
--   6. on the same set as in 3, the function $G$ minus its polar parts is small:
--   $$\Bigl|G(s)-\sum_{p\in P}\frac{r(p)}{s-p}\Bigr|\;\le\;C_0\log^2\bigl(q(|t|+2)\bigr)\qquad(\sigma\ge1-c/\log(q(|t|+2)),\ \sigma\ge\tfrac34,\ s\notin P).$$
--
--   Then for every integer $N\ge2$ with $q\le\exp(c_2\sqrt{\log N})$,
--   $$\Bigl|\sum_{n<N}a(n)\;-\;\sum_{p\in P}r(p)\frac{N^{p}}{p}\Bigr|\;\le\;C\,N\exp\bigl(-c_1\sqrt{\log N}\bigr).$$
--
--   This is the analytic engine of the prime number theorem with de la Vallée Poussin error term (Davenport §18) and of its character version (§§19–20), stated once for an arbitrary Dirichlet series with von Mangoldt-size coefficients so that it applies verbatim to $-\zeta'/\zeta$ (with $P=\{1\}$, $r(1)=1$), to $-L'/L(s,\chi_0)$ for the principal character, and to $-L'/L(s,\chi)$ for a non-principal character with an exceptional zero $\beta$ (with $P=\{\beta\}$ and $r(\beta)=-m_\beta$, producing the term $-m_\beta N^{\beta}/\beta$). The proof is the classical contour argument: represent a smoothed version of the partial sum as a vertical integral of $G(s)\,\widehat{w}(s)\,N^{s}$ on $\sigma=1+1/\log N$, subtract the explicit polar parts (whose contribution is evaluated exactly by shifting far to the left), shift the remaining integral to $\sigma_1=1-c'/\log(qT)$ with $T=\exp(\sqrt{\log N})$ inside the region where hypothesis 6 applies, and choose the smoothing width $\varepsilon=\exp(-c''\sqrt{\log N})$; the hypothesis $q\le\exp(c_2\sqrt{\log N})$ ensures $N^{\sigma_1}\le N\exp(-c_1\sqrt{\log N})$.
--
--   **Formalization Note.** The region is `InRegion c q s`, i.e. $1-c/\log(q(|\operatorname{Im}s|+2))\le\operatorname{Re}s$; analyticity is `AnalyticOnNhd`; $\sum_{n\ge1}a(n)n^{-s}$ is Mathlib's `LSeries a s` (whose $n=0$ term is $0$, and $a(0)=0$ is forced by hypothesis 1); the partial sum is over $0\le n<N$; $N^{p}$ is the complex power of the positive real $N$. Since $\operatorname{Re}p\ge1/2$, the quotient $N^p/p$ is well defined.
--
--   **Provenance.** This statement is the prove2.me theorem `Davenport.perron_of_region_bound` (e1f52231-1959-47c4-9cfb-ac1eb539c322, statement by alya), published in the Mathlib c5ea003 (Lean 4.30.0) environment, here re-published unchanged in substance under the `SWPort` namespace for the Mathlib 0df444a environment. Its proof is a port of the accepted submission ea5571ed-35e5-4b15-af08-e7266dcc30ca by alya, carved so that each piece fits the verifier. The port serves the Siegel–Walfisz theorem used by OpenAI's *Primitive roots for every admissible integer base* (2026), published as `ArtinPrimitiveRoots.siegel_walfisz`. The text above is the original author's natural-language statement.
-- source:
--   prove2.me user alya's proof of the Siegel–Walfisz theorem, Davenport.siegel_walfisz_ap (ff9f3207-eba1-492e-9691-e50480292b68, Mathlib c5ea003), following H. Davenport, Multiplicative Number Theory; ported to Mathlib 0df444a; original statement Davenport.perron_of_region_bound (e1f52231-1959-47c4-9cfb-ac1eb539c322) by alya

import Mathlib
import Definitions.Def_SWPort_001

section

namespace SWPort

open Finset DirichletCharacter Vino
open Complex Real Set MeasureTheory intervalIntegral Filter Topology

open Davenport in
theorem _root_.SWPort.Davenport.perron_of_region_bound (c C₀ : ℝ) (hc : 0 < c) (hC₀ : 0 < C₀) :
    ∃ c₁ c₂ C : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (a : ℕ → ℂ) (G : ℂ → ℂ) (P : Finset ℂ) (r : ℂ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n) →
        (∀ s : ℂ, 1 < s.re → G s = LSeries a s) →
        AnalyticOnNhd ℂ G ({s : ℂ | InRegion c q s ∧ 3 / 4 ≤ s.re} \ ↑P) →
        (∀ p ∈ P, 1 / 2 ≤ p.re ∧ p.re ≤ 1) →
        (∑ p ∈ P, ‖r p‖) ≤ C₀ * Real.log (2 * q) →
        (∀ s : ℂ, InRegion c q s → 3 / 4 ≤ s.re → s ∉ P →
            ‖G s - ∑ p ∈ P, r p / (s - p)‖ ≤ C₀ * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2) →
        ∀ N : ℕ, 2 ≤ N → (q : ℝ) ≤ Real.exp (c₂ * Real.sqrt (Real.log N)) →
          ‖(∑ n ∈ range N, a n) - ∑ p ∈ P, r p * (N : ℂ) ^ p / p‖
            ≤ C * N * Real.exp (-c₁ * Real.sqrt (Real.log N)) := by
  sorry

end SWPort
end
