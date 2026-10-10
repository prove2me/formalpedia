-- Prove2me | Theorems.Thm_RieszMF_Global_proposition_5_12
-- name    : RieszMF.Global.proposition_5_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:49.844989+00:00
-- url     : https://prove2.me/theorems/526f6ffd-1f61-4cba-b4a1-83e73850bd7a
-- title:
--   Proposition 5.12, p. 26 — smeared-energy bound via an extension $\mathsf G$ for $d-2<s<d$
-- statement:
--   Let $d\ge3$ and $d-2<s<d$. Let $h:\mathbb R^d\to\mathbb R$ satisfy (i), (iii) with $r_0=\infty$ and (iv) of order $s$, and let $\mathsf G:\mathbb R^{d+m}\setminus\{0\}\to\mathbb R$, $m\ge1$, be an extension, $\mathsf G(x,0)=h(x)$, which is even, superharmonic on $\mathbb R^{d+m}\setminus\{0\}$, smooth there with $|\nabla^{\otimes k}\mathsf G(X)|\le C_k|X|^{-(s+k)}$, and has $\hat{\mathsf G}\ge0$ away from $0$. There is $C>0$, depending only on $s,d,h,\mathsf G$, such that for every pairwise distinct $x_N$, every probability density $\mu\in L^\infty$ and every $\eta_1,\dots,\eta_N>0$,
--
--   $$\frac1{N^2}\sum_{1\le i\ne j\le N}\big(h(x_j-x_i)-\mathsf G_{\eta_i}(x_j-x_i,0)\big)_+\le F_N(x_N,\mu)+\frac CN\sum_{i=1}^N\Big(\frac{\eta_i^{-s}}N+\|\mu\|_{L^\infty}\eta_i^{d-s}\Big),$$
--
--   where $\mathsf G_\eta=\mathsf G*\delta^{(\eta)}_0$ is the average over spheres of radius $\eta$ in $\mathbb R^{d+m}$ and $F_N$ is the modulated energy of $h$.
--
--   This is the super-Coulombic counterpart of Remark 5.11, used by Corollary 5.14 for $-\Delta\mathsf g$ when $d-4<s<d-2$.
--
--   **Formalization Note** The page refers to (1.14)–(1.17), whose derivative bound (1.16) has exponent $s+2+k$ because in (viii) $\mathsf G$ extends $-\Delta\mathsf g$, of order $s+2$. Here $\mathsf G$ extends a potential of order $s$, so the bound is read with exponent $s+k$; Corollary 5.14 applies the proposition with $s+2$ in place of $s$, which recovers (1.16). The statement is for a generic potential $h$ of order $s$.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 26, Proposition 5.12, (5.34)

import Mathlib
import Definitions.Def_RieszMF_Global_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace RieszMF.Global

/-- Proposition 5.12 (p. 26), (5.34): for `d ≥ 3`, `d - 2 < s < d`, a potential `h` of order `s`
with (i), (iii) for `r₀ = ∞`, (iv), and an extension `G : ℝ^{d+m} ∖ {0} → ℝ`, `G(x, 0) = h(x)`,
with (1.14)–(1.17) for `r₀ = ∞` (the derivative bounds (1.16) at the order `s` of `h`), there is
`C > 0` such that for every pairwise distinct `x_N`, every `μ ∈ 𝒫 ∩ L^∞` and all `η_i > 0`,
`(1/N²) ∑_{i≠j} (h(x_j - x_i) - G_{η_i}(x_j - x_i, 0))_+ ≤ F_N(x_N, μ)
  + (C/N) ∑_i (η_i^{-s}/N + ‖μ‖_{L^∞} η_i^{d-s})`. -/
theorem proposition_5_12 :
    ∀ (d : ℕ) (s : ℝ), 3 ≤ d → (d : ℝ) - 2 < s → s < (d : ℝ) →
    ∀ h : RieszMF.Linear.E d → ℝ, RieszMF.Linear.AssumpI h → GloballySuperharmonic h → RieszMF.Linear.AssumpIV d s h →
    ∀ (m : ℕ), 0 < m → ∀ G : RieszMF.Linear.E (d + m) → ℝ, IsGlobalExtension d m h s G →
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 0 < N →
    ∀ x : Fin N → RieszMF.Linear.E d, Pairwise (fun i j => x i ≠ x j) →
    ∀ μ : RieszMF.Linear.E d → ℝ, IsProbDensity μ →
    ∀ η : Fin N → ℝ, (∀ i, 0 < η i) →
      smearGapExt N h G x η ≤
        RieszMF.Linear.modEnergy N h x μ +
          C / N * ∑ i, (η i ^ (-s) / N + supNorm μ * η i ^ ((d : ℝ) - s)) := by sorry

end RieszMF.Global
