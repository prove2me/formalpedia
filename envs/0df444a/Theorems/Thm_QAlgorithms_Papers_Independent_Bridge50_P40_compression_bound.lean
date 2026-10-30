-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P40_compression_bound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P40.compression_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:01:41.264253+00:00
-- url     : https://prove2.me/theorems/d3a377bd-c923-4098-81ea-1a4c980ee99e
-- title:
--   Finite-block strong converse for Schumacher compression
-- statement:
--   All registers are finite and nonempty. Density operators have trace one, pure states are normalized, all entropies and logarithms are in base two, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Write $S_a$ for Petz Rényi entropy, with support projection at order zero and the von Neumann limit at order one; $S_\infty(\rho)=-\log_2\lambda_{\max}(\rho)$.
--
--   Let $\rho^A$ be a density operator with normalized purification $\psi^{RA}$. For $n\ge1$, let $\mathcal C:A^n\to B$ and $\mathcal D:B\to A_1^n$ be arbitrary CPTP compression and decompression maps, with $A_1$ identified with $A$. Let $0\le F\le1$ be a lower bound on the root fidelity between the complete reference-entangled output $(\mathrm{id}_{R^n}\otimes\mathcal D\mathcal C)(\psi^{\otimes n})$ and the same source purification. For $\tfrac12<a<1$ and $b=a/(2a-1)$,
--
--   $$
--   F\le2^{\frac{n(1-a)}{2a}\left[\frac{\log_2\dim B}{n}-S_b(\rho)\right]}.
--   $$
--
--   The transmitted dimension is arbitrary and nonzero. This uses reference-entangled fidelity, not average ensemble fidelity, and includes zero fidelity.
-- source:
--   A strong converse for the quantum state merging protocol, arXiv:1404.5940v1, PDF p. 12, Theorem 13, equation (61)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P40

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply marginalAR)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (cq)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.12, Theorem 13, (61): arbitrary CPTP compression and decompression,
measured against the same reference-entangled source purification. -/
theorem compression_bound {A R B : Type} [Fintype A] [Fintype R] [Fintype B]
    [Nonempty A] [Nonempty R] [Nonempty B]
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (R × A)) (hpsi : IsState psi)
    (hpur : traceLeft (pureDensity psi) = rho)
    (n : ℕ) (hn : 0 < n) (C : Superop (Fin n → A) B) (hC : IsChannel C)
    (D : Superop B (Fin n → A)) (hD : IsChannel D)
    (F a : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (hF : F ≤ compressionFidelity psi n C D) (ha : (1 : ℝ) / 2 < a) (ha1 : a < 1) :
    F ≤ (2 : ℝ) ^ ((n : ℝ) * (1 - a) / (2 * a) *
      (Real.logb 2 (Fintype.card B) / (n : ℝ) - renyiEntropy (a / (2 * a - 1)) rho)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P40

end
