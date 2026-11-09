-- Prove2me | Theorems.Thm_RGGThreshold_lemma_5_4
-- name    : RGGThreshold.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:00:44.245836+00:00
-- url     : https://prove2.me/theorems/ddfd8d8c-6446-48cd-ac34-4669dcd7d6df
-- title:
--   Lemma 5.4 — the one-step expectation bound
-- statement:
--   Assume Setup (⋆) for the vertex $s$ ($1\le s<n$) with revealed data satisfying $\Pi_{s-1}$, and the standing hypotheses ($H\in\mathcal E(K^{\mathcal E})$, $1/3\ge p\ge n^{-1/3}(\log n)^A$, $d\ge Cn^2p(\log n)^A$, $\mathbb P[\langle x_1,x_2\rangle\ge\tau]=p$). Then, with the expectation over the new column $v_{s+1}(s),\dots,v_n(s)$,
--
--   $$
--   \mathbb E\Big[\mathbf 1_{\mathcal T_s}e^{Z_s-Z_{s-1}}\prod_{s<i<j\le n}\frac{\Phi_{sij}}{\Phi_{s-1,ij}}\Big]\le\exp\Big(\frac1{\sqrt d}\sum_{s<i<j\le n}\lambda_{si}\lambda_{sj}\lambda_{ij}-\frac1{2d}\sum_{s<i<j\le n}\lambda_{si}^2\lambda_{sj}^2\lambda_{ij}^2+\frac1d\sum_{\substack{s<r\le n\\ s<i<j\le n}}\lambda_{si}\lambda_{sj}\lambda_{ri}\lambda_{rj}
--   +\frac1d\sum_{\substack{s<r\le n\\ s<i<j\le n}}\lambda_{si}\lambda_{sj}\lambda_{ri}\lambda_{rj}\big[\lambda_{ij}(z_p-\lambda_{ij})+\lambda_{sr}(z_p-\lambda_{sr})\big]+\tilde O(R_{n,d,p})\Big).
--   $$
--
--   The right side is $f(H_{s-1})-f(H_s)$ for the signed-count exponent $f$, up to a nonpositive term and the error; this is the estimate that closes the induction of Lemma 5.1.
--
--   **Formalization Note** The constants are quantified as $\exists A,\ \forall K^{\mathcal E}>0,\ \exists C>0,\ \exists C',B,N$, then $n\ge N$ and the rest; $\tilde O(X)$ is $C'(\log(nd))^BX$. The statement is deterministic in the revealed data: they are any coordinate matrix satisfying $\Pi_{s-1}$. The expectation of the nonnegative integrand is a lower Lebesgue integral with values in $[0,\infty]$. The sums over $r$ include $r=i,j$, where $\lambda_{ii}=0$. The paper's vertex $s$ is the 0-based vertex $v$.
--
--   Differences from the source:
--
--   - reading: "for every constant K^𝓔 > 0, there is a constant C and a large absolute constant A" → ∃ A, ∀ K > 0, ∃ C > 0; reason: A is absolute, so it does not depend on K^𝓔; this is the stronger of the two orders
--   - reading: Õ(X) ("constant-power logarithmic terms depending on n, p and d", §4.1) → C'·(log(nd))^B·X with C', B chosen after K and C and before n, p, d, H and the data; reason: uniform constants are what §4.1 allows; log(1/p) ≤ log n on the range p ≥ n^{-1/3}
--   - reading: the asymptotic statement holds for large n → ∃ N, ∀ n ≥ N after the constants; reason: "n large" made explicit
--   - encoding: A a large absolute (real) constant → A : ℕ, used as (log n)^A; reason: for n ≥ 3, raising A to ⌈A⌉ only shrinks the p-range, so the two forms are equivalent
--   - reading: "Assume Setup (⋆)": revealed coordinates v_i(j), j ≤ s−1, satisfying Π_{s−1} → any real matrix W whose first s−1 columns satisfy Π_{s−1}; reason: every such matrix is realized by revealed coordinates once Π_{s−1} makes the rows i ≥ s shorter than 1, which holds for large n
--   - encoding: the expectation E[·] of a nonnegative quantity → lower Lebesgue integral ∫⁻ of ENNReal.ofReal of the integrand; reason: same value for a nonnegative measurable integrand, with no integrability side condition
--   - encoding: the threshold c_{p,d}/√d with P[⟨x_i,x_j⟩ ≥ c_{p,d}/√d] = p → any τ with capProb d τ = p; reason: for d ≥ 2 this τ is unique and equals c_{p,d}/√d; the Lean statement holds for every solution
--   - encoding: vertices and coordinates 1, …, n → Fin n, numbered from 0; reason: index shift only; each statement shifts s accordingly
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Lemma 5.4, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_RGGThreshold_InE
import Definitions.Def_RGGThreshold_eventF
import Definitions.Def_RGGThreshold_PhiS
import Definitions.Def_RGGThreshold_kappaTri
import Definitions.Def_RGGThreshold_setupStar

open MeasureTheory

namespace RGGThreshold

open Classical in
/-- **Lemma 5.4** (Hunter–Milojević–Sudakov, *Distinguishability Threshold for Random Geometric Graphs*, arXiv:2607.22480, held version, sha256 1a398ef9…, Lemma 5.4, p.19 (PDF p.21)). Assume Setup (⋆) and the standing hypotheses.
Then
`E[1_{T_s} e^{Z_s - Z_{s-1}} ∏_{s<i<j≤n} Φ_{sij}/Φ_{s-1,ij}] ≤ exp((1/√d) ∑_{s<i<j≤n} λ_{si}λ_{sj}λ_{ij}
 - (1/2d) ∑_{s<i<j≤n} λ_{si}²λ_{sj}²λ_{ij}² + (1/d) ∑_{s<r≤n, s<i<j≤n} λ_{si}λ_{sj}λ_{ri}λ_{rj}
 + (1/d) ∑_{s<r≤n, s<i<j≤n} λ_{si}λ_{sj}λ_{ri}λ_{rj}[λ_{ij}(z_p - λ_{ij}) + λ_{sr}(z_p - λ_{sr})] + Õ(R_{n,d,p}))`.

**Formalization Note** The standing hypotheses (Proposition 2.1; §5, p.14: "the hypotheses of Proposition 2.1 remain
in force") are read with the quantifier order `∃ A, ∀ K^𝓔 > 0, ∃ C > 0`, then the `Õ`-constants
`C', B` and the threshold `N` for "large `n`", then `n, p, d, τ, H` and the rest. `Õ(X)` is
`C' (log(nd))^B X`; the threshold `c_{p,d}/√d` is any `τ` with `P[⟨x_1, x_2⟩ ≥ τ] = p` (`capProb`). The statement is deterministic in the revealed data: `W` is
any coordinate matrix (only its columns `< v` are read) satisfying `Π_{s-1}` (`projW d v W`), as
in Setup (⋆). The paper's vertex `s` is the 0-based vertex `v` (`s = v + 1`), the expectation is
over the new column `u ∼ setupStar d τ H v W`, and the matrix after revealing it is
`extendCol v W u`. The expectation of the nonnegative integrand is a lower Lebesgue integral in
`[0, ∞]`. The sums over `r` include `r = i, j` (`λ_{ii} = 0`). -/
theorem lemma_5_4 :
    ∃ A : ℕ, ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∃ (C' : ℝ) (B N : ℕ),
    ∀ n : ℕ, N ≤ n → ∀ p : ℝ, (n : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log n ^ A ≤ p → p ≤ 1 / 3 →
    ∀ d : ℕ, C * (n : ℝ) ^ 2 * p * Real.log n ^ A ≤ d →
    ∀ τ : ℝ, RGGDetect.capProb d τ = p →
    ∀ H : SimpleGraph (Fin n), InE K n p H →
    ∀ v : Fin n, v.val + 1 < n →
    ∀ W : Fin n → Fin n → ℝ, projW d v.val W →
    ∫⁻ u, ENNReal.ofReal
        ((if truncW d (v.val + 1) (extendCol v W u) then 1 else 0) *
          Real.exp (Zs p H (v.val + 1) (extendCol v W u) - Zs p H v.val W) *
          ∏ i : Fin n, ∏ j : Fin n,
            if v < i ∧ i < j then
              PhiS p d H (v.val + 1) (extendCol v W u) i j / PhiS p d H v.val W i j
            else 1)
      ∂(setupStar d τ H v W) ≤
    ENNReal.ofReal (Real.exp (
      1 / Real.sqrt d * (∑ i : Fin n, ∑ j : Fin n,
        if v < i ∧ i < j then lam p H v i * lam p H v j * lam p H i j else 0) -
      1 / (2 * d) * (∑ i : Fin n, ∑ j : Fin n,
        if v < i ∧ i < j then lam p H v i ^ 2 * lam p H v j ^ 2 * lam p H i j ^ 2 else 0) +
      1 / d * (∑ r : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        if v < r ∧ v < i ∧ i < j then
          lam p H v i * lam p H v j * lam p H r i * lam p H r j else 0) +
      1 / d * (∑ r : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        if v < r ∧ v < i ∧ i < j then
          lam p H v i * lam p H v j * lam p H r i * lam p H r j *
            (lam p H i j * (zp p - lam p H i j) + lam p H v r * (zp p - lam p H v r))
        else 0) +
      C' * Real.log ((n : ℝ) * d) ^ B * Rerr n d p)) := by sorry

end RGGThreshold
