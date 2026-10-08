-- Prove2me | Theorems.Thm_RobustPCA_Recovery_theorem_1_1
-- name    : RobustPCA.Recovery.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:57.449976+00:00
-- url     : https://prove2.me/theorems/429b6866-5b25-4262-8bcf-2cd849456489
-- title:
--   Theorem 1.1 — Principal Component Pursuit with $\lambda=1/\sqrt n$ is exact with probability $1-cn^{-10}$
-- statement:
--   There are positive numerical constants $c$, $\rho_r$ and $\rho_s$ with the following property. Let $n\ge1$ and let $L_0\in\mathbb R^{n\times n}$ have rank $r$ and compact SVD $L_0=\sum_{k=1}^r\sigma_ku_kv_k^*$, $U=[u_1,\dots,u_r]$, $V=[v_1,\dots,v_r]$, obeying the incoherence condition with parameter $\mu$:
--   $$\max_i\|U^*e_i\|^2\le\frac{\mu r}{n},\qquad\max_i\|V^*e_i\|^2\le\frac{\mu r}{n},\qquad\|UV^*\|_\infty\le\sqrt{\frac{\mu r}{n^2}}.\tag{1.2–1.3}$$
--   Let $S\in\mathbb R^{n\times n}$ be an arbitrary fixed matrix, let $\Omega$ be uniformly distributed among all subsets of $[n]\times[n]$ of cardinality $m$, and let $S_0=\mathcal P_\Omega S$. If
--   $$\operatorname{rank}(L_0)\le\rho_r\,n\,\mu^{-1}(\log n)^{-2}\qquad\text{and}\qquad m\le\rho_s\,n^2,\tag{1.4}$$
--   then with probability at least $1-c\,n^{-10}$ (over the choice of $\Omega$), Principal Component Pursuit
--   $$\text{minimize }\|L\|_*+\frac1{\sqrt n}\|S'\|_1\quad\text{subject to}\quad L+S'=L_0+S_0$$
--   is exact: its unique solution is $(L_0,S_0)$.
--
--   A low-rank matrix with spread-out singular vectors can thus be separated from a constant fraction of arbitrary gross errors at random locations by a single convex program with a universal weight and no tuning.
--
--   **Formalization Note** The constants $c,\rho_r,\rho_s$ are quantified before all data. $S_0=\mathcal P_\Omega S$ is the paper's model for the sparse component (p. 6): the magnitudes and signs are arbitrary and fixed, and the support is random. The rank $r$ is carried by the SVD data; the rank condition is written multiplied out, $r\mu(\log n)^2\le\rho_rn$, which avoids division by $\mu$ and $\log n$. $\log$ is natural. Only the square case is stated.
-- source:
--   Candès, Li, Ma, Wright, Robust principal component analysis?, J. ACM 58(3) (2011), p. 5, Theorem 1.1 (first sentence, square case), with (1.1)–(1.4) pp. 4–5 and the model for S0 on p. 6

import Definitions.Def_RobustPCA_Recovery_Setup
open MatrixCompletion

namespace RobustPCA.Recovery

/-- Theorem 1.1, p. 5 (square case): there are numerical constants `c, ρr, ρs > 0` such
that, if `L0` is `n × n` and obeys (1.2)–(1.3), `rank(L0) ≤ ρr n μ⁻¹ (log n)⁻²`, and
`S0 = 𝒫_Ω S` for an arbitrary fixed `S` and a support `Ω` uniformly distributed among all sets of
cardinality `m ≤ ρs n²`, then with probability at least `1 − c n⁻¹⁰` Principal Component Pursuit
(1.1) with `λ = 1/√n` is exact: its unique solution is `(L0, S0)`. -/
theorem theorem_1_1 :
    ∃ c ρr ρs : ℝ, 0 < c ∧ 0 < ρr ∧ 0 < ρs ∧
      ∀ (n r m : ℕ) (L0 S : RealMatrix n n) (SV : SVD L0 r) (μ : ℝ),
        0 < n → Incoherent SV μ →
        (r : ℝ) * μ * Real.log n ^ 2 ≤ ρr * n →
        (m : ℝ) ≤ ρs * (n : ℝ) ^ 2 →
        fixedCardinalityEventProb m
            (fun Ω => IsPCPExact (1 / Real.sqrt n) L0 (samplingProjection Ω S)) ≥
          1 - c * (n : ℝ) ^ (-10 : ℤ) := by sorry

end RobustPCA.Recovery
