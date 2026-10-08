-- Prove2me | Theorems.Thm_RobustPCA_Recovery_lemma_3_2
-- name    : RobustPCA.Recovery.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:55.069891+00:00
-- url     : https://prove2.me/theorems/e968d4ba-cfc8-470d-898c-69288a3c4388
-- title:
--   Lemma 3.2 ([8, Thm 6.3]) — $\|(\mathcal I-\rho_0^{-1}\mathcal P_{\Omega_0})Z\|\le C_0'\sqrt{n\log n/\rho_0}\,\|Z\|_\infty$
-- statement:
--   There are numerical constants $C_0>0$, $C_0'>0$ and $c>0$ with the following property. Let $n\ge1$, $\mu\ge1$, let $Z\in\mathbb R^{n\times n}$ be a fixed matrix, let $0<\rho_0\le1$ with
--   $$\rho_0\ge C_0\,\frac{\mu\log n}{n},$$
--   and let $\Omega_0\sim\mathrm{Ber}(\rho_0)$ (each entry independently with probability $\rho_0$). Then with probability at least $1-c\,n^{-10}$,
--   $$\|(\mathcal I-\rho_0^{-1}\mathcal P_{\Omega_0})Z\|\le C_0'\sqrt{\frac{n\log n}{\rho_0}}\;\|Z\|_\infty,\tag{3.2}$$
--   where $\|\cdot\|$ is the operator norm and $\|Z\|_\infty=\max_{ij}|Z_{ij}|$.
--
--   This spectral-norm bound for a randomly sampled fixed matrix (from Candès–Recht) controls $\|W^L\|$ in Lemma 2.8.
--
--   **Formalization Note** $\mu$ appears only in the sampling threshold; $\mu\ge1$ holds for the incoherence parameter of every $L_0$ of rank at least one, and without it the threshold would allow arbitrarily small $\rho_0$, for which (3.2) fails.
-- source:
--   Candès, Li, Ma, Wright, Robust principal component analysis?, J. ACM 58(3) (2011), p. 17, Lemma 3.2 (= Candès–Recht 2009, Theorem 6.3)

import Definitions.Def_RobustPCA_Recovery_Setup
open MatrixCompletion

namespace RobustPCA.Recovery

/-- Lemma 3.2 ([8, Theorem 6.3]), p. 17: there are numerical constants `C0, C0', c > 0`
such that, for a fixed `Z` and `Ω0 ∼ Ber(ρ0)` with `ρ0 ≥ C0 μ log n / n` (`μ ≥ 1`), with
probability at least `1 − c n⁻¹⁰`, `‖(I − ρ0⁻¹ 𝒫_{Ω0}) Z‖ ≤ C0' √(n log n / ρ0) ‖Z‖_∞`. -/
theorem lemma_3_2 :
    ∃ C0 C0' c : ℝ, 0 < C0 ∧ 0 < C0' ∧ 0 < c ∧
      ∀ (n : ℕ) (Z : RealMatrix n n) (μ ρ0 : ℝ),
        0 < n → 1 ≤ μ → 0 < ρ0 → ρ0 ≤ 1 → ρ0 ≥ C0 * μ * Real.log n / n →
        bernoulliEventProb ρ0 (fun Ω =>
            spectralNorm (Z - ρ0⁻¹ • samplingProjection Ω Z) ≤
              C0' * Real.sqrt (n * Real.log n / ρ0) * entrySupNorm Z) ≥
          1 - c * (n : ℝ) ^ (-10 : ℤ) := by sorry

end RobustPCA.Recovery
