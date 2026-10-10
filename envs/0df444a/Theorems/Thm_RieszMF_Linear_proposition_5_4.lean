-- Prove2me | Theorems.Thm_RieszMF_Linear_proposition_5_4
-- name    : RieszMF.Linear.proposition_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:47.921316+00:00
-- url     : https://prove2.me/theorems/6a1122f8-65ba-4741-a724-5f6e84a35672
-- title:
--   Proposition 5.4, p. 23 — smeared lower bound for $F_N$ when $d-2<s<d$, through an extension $\mathsf G$ to $\mathbb R^{d+m}$
-- statement:
--   Let $d\ge3$ and $d-2<s<d$. Let $\mathsf g:\mathbb R^d\setminus\{0\}\to\mathbb R$ and $\mathsf G:\mathbb R^{d+m}\setminus\{0\}\to\mathbb R$, $m\ge1$, with $\mathsf g(x)=\mathsf G(x,0)$ and (1.14)–(1.17): $\mathsf G$ even, superharmonic and smooth in $B(0,r_0)\setminus\{0\}$, $|\nabla^{\otimes k}\mathsf G(X)|\le C_k|X|^{-(s+k)}$ there, and $\hat{\mathsf G}\ge0$ off the origin. There is $C>0$ depending only on $s,d,\mathsf g,\mathsf G$ such that for every $N\ge1$, every pairwise distinct $x_N\in(\mathbb R^d)^N$, every $\mu\in\mathcal P(\mathbb R^d)\cap L^\infty(\mathbb R^d)$ and every $0<\eta_1,\dots,\eta_N<\min\{\frac12,\frac{r_0}2\}$,
--   $$\frac1{N^2}\sum_{\substack{1\le i\ne j\le N\\|x_i-x_j|\le r_0/2}}\big(\mathsf g(x_j-x_i)-\mathsf G_{\eta_i}(x_j-x_i,0)\big)_+\le F_N(x_N,\mu)+\sum_{i=1}^N\frac{\eta_i^{-s}(1+|\log\eta_i|\mathbf 1_{s=0})}{N^2}+\frac CN\sum_{i=1}^N\big(\|\mu\|_{L^\infty}\eta_i^{d-s}+\eta_i^2\big),$$
--   with $\mathsf G_\eta=\mathsf G*\delta_0^{(\eta)}$ the average of $\mathsf G$ over spheres of radius $\eta$ in $\mathbb R^{d+m}$.
--
--   Superharmonicity fails in $\mathbb R^d$ for these potentials but is restored in the extended space; Corollary 5.6 uses this with $-\Delta\mathsf g$ in the range $d-4<s<d-2$.
--
--   **Formalization Note.** Here $\mathsf G$ extends a potential of order $s$, so (1.16) is read with exponent $s+k$ (in (viii) the extension of $-\Delta\mathsf g$ has order $s+2$). The integrals defining $F_N(x_N,\mu)$ are assumed absolutely convergent: the proposition places no condition on $\mathsf g$ outside $B(0,r_0)$, and the printed inequality presupposes that $F_N$ is defined.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 23, Proposition 5.4, (5.12), (5.16)

import Mathlib
import Definitions.Def_RieszMF_Linear_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal FourierTransform Laplacian

namespace RieszMF.Linear

theorem proposition_5_4 (d : ℕ) (hd : 3 ≤ d) (s : ℝ) (hs1 : (d : ℝ) - 2 < s) (hs2 : s < d)
    (g : E d → ℝ) (m : ℕ) (hm : 0 < m) (G : E (d + m) → ℝ) (r₀ : ℝ)
    (hgG : ∀ x : E d, x ≠ 0 → g x = G (embed d m x)) (hG : ExtensionConds (d + m) s G r₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ x : Fin N → E d, Pairwise (fun i j => x i ≠ x j) →
      ∀ μ : E d → ℝ, IsProbDensityLinfty μ → OffDiagIntegrable N (fun a b => g (a - b)) x μ →
      ∀ η : Fin N → ℝ, (∀ i, 0 < η i ∧ η i < min (1 / 2) (r₀ / 2)) →
        (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ (Finset.univ.erase i).filter (fun j => ‖x i - x j‖ ≤ r₀ / 2),
            max (g (x j - x i) - smear G (η i) (embed d m (x j - x i))) 0
          ≤ modEnergy N g x μ
            + ∑ i, η i ^ (-s) * (1 + |Real.log (η i)| * (if s = 0 then 1 else 0)) / (N : ℝ) ^ 2
            + (C / N) * ∑ i, (lpNorm μ ⊤ * η i ^ ((d : ℝ) - s) + η i ^ 2) := by sorry

end RieszMF.Linear
