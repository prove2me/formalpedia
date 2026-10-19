-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapL01_classicalShadow_prediction
-- name    : QAlgorithms.Papers.RoadmapL01.classicalShadow_prediction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:29:18.593704+00:00
-- url     : https://prove2.me/theorems/b7940fe9-569b-425b-a7a1-071b2f7828d2
-- title:
--   Classical shadows: simultaneous linear prediction by median of means
-- statement:
--   Let $n\ge0$, $d=2^n$, and let $\rho$ be any density matrix on an $n$-qubit system. Fix a tomographically complete measurement primitive: a probability ensemble $\mu$ of unitary matrices, whose averaged measurement channel $\mathcal M$ is invertible. A shot samples $U\sim\mu$, measures $U\rho U^\dagger$ in the computational basis with Born outcome $b$, and forms the snapshot $\widehat\rho=\mathcal M^{-1}(U^\dagger|b\rangle\langle b|U)$. The ensemble may be continuous and need not be uniform.
--
--   Fix $M\ge1$ Hermitian observables $O_1,\ldots,O_M$, independently of the sampled outcomes, and $0<\varepsilon\le1$, $0<\delta\le1$. For a Hermitian matrix $A$, define
--
--   $$
--   \|A\|_{\mathrm{shadow}}^2=\max_{\sigma\text{ a density matrix}}\mathbb E_{U\sim\mu}\sum_{b\in\{0,1\}^n}\langle b|U\sigma U^\dagger|b\rangle\,\langle b|U\mathcal M^{-1}(A)U^\dagger|b\rangle^2.
--   $$
--
--   Set $V=\max_{1\le i\le M}\|O_i-\operatorname{tr}(O_i)I/d\|_{\mathrm{shadow}}^2$, $K=\lceil2\log(2M/\delta)\rceil$, and $N=\max\{1,\lceil34V/\varepsilon^2\rceil\}$. Here $\log$ is natural logarithm. Draw exactly $KN$ independent snapshots in $K$ batches of $N$ shots. Let $\widehat o_i$ be the median of the $K$ batch means of $\operatorname{tr}(O_i\widehat\rho)$, using the lower median for even $K$. Then
--
--   $$
--   \Pr\!\left[\forall i\in\{1,\ldots,M\},\quad |\widehat o_i-\operatorname{tr}(O_i\rho)|\le\varepsilon\right]\ge1-\delta.
--   $$
--
--   This is the paper's simultaneous linear-prediction guarantee, with observable-dependent sample size and no purity, locality, positivity, operator-norm, or computational-cost restriction on the observables.
--
--   **Formalization Note** The printed zero endpoints in (S13) are undefined and are excluded. Integer counts are rounded upward and each batch has at least one sample, including scalar observables with $V=0$. Lean concludes positivity of the constructed counts instead of assuming it. Real parts of traces express the real expectations of Hermitian observables.
-- source:
--   Predicting Many Properties of a Quantum System from Very Few Measurements, arXiv:2002.08953v2, Supplementary Information §1.B, Theorem 1, Eqs. (S13)–(S14), PDF p. 13. https://arxiv.org/abs/2002.08953v2 . PDF SHA-256: 7d0b0d0896354d6261fa36f3e4b5ed79c5b0334c966310d5d516e53671e0eef5.

import Definitions.Def_QAlgorithms_Defs_ClassicalShadowPrediction
set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QAlgorithms.Papers.RoadmapL01

open QAlgorithms.ClassicalShadows

/-- Huang, Kueng and Preskill, arXiv:2002.08953v2, supplementary Theorem 1,
PDF p.13, Eqs. (S13)--(S14). Primitive and snapshots: p.11, Eqs. (S1)--(S3);
shadow norm and median of means: p.12, Eqs. (S7), (S12).
The queued p.3 locator is the informal version, continuing on p.4.

The printed zero endpoints for eps and delta make (S13) undefined and are excluded;
the upper endpoints are retained. The frozen sampleSchedule rounds K and N upward
and takes N at least one, including when every centered observable is zero.
Positivity witnesses are conclusions, not additional assumptions. The K-by-N array
uses exactly K*N independent copies. For even K the frozen lower median fixes the
source's unspecified tie convention. Completeness means invertibility of the
averaged channel, including for continuous or nonuniform ensembles.
No unbiasedness, variance bound, or snapshot trace property is assumed. -/
theorem classicalShadow_prediction
    {n M : ℕ} (P : MeasurementPrimitive n)
    (O : Fin M → Space n) (hO : ∀ i, (O i).IsHermitian) (hM : 0 < M)
    (rho : Space n) (hrho : IsDensityMatrix rho)
    (eps delta : ℝ) (heps : 0 < eps ∧ eps ≤ 1) (hdelta : 0 < delta ∧ delta ≤ 1) :
    let counts := sampleSchedule P O hO hM eps delta heps hdelta
    ∃ (hK : 0 < counts.1) (hN : 0 < counts.2),
      ENNReal.ofReal (1 - delta) ≤
        arrayLaw P rho hrho counts.1 counts.2
          {shots | ∀ i : Fin M,
            |medianOfMeans P (O i) counts.1 counts.2 hK hN shots -
              ((O i) * rho).trace.re| ≤ eps} := by sorry

end QAlgorithms.Papers.RoadmapL01
