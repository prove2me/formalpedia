-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_invariant_local_events
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.invariant_local_events
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:55:26.150388+00:00
-- url     : https://prove2.me/theorems/35a60d0b-129e-4506-a695-03ad41ca1ce0
-- title:
--   Lemma 5.3: stabilizer-invariant shrinking events attain the local exponent
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   A scheme with rate $I$ satisfies the closed-set upper and open-set lower large-deviation bounds for every input; $I(\rho,\cdot)$ is good and vanishes exactly at the target of $\rho$.
--
--   For a full scheme with rate $I$ and fixed states $\rho,\sigma$, there is a sequence of Borel events $\Delta_N$ such that
--   $$\mu_{N,\sigma}(\Delta_N)\longrightarrow1,\qquad -\frac1N\log\mu_{N,\rho}(\Delta_N)\longrightarrow I(\rho,\sigma),$$
--   and $U\Delta_NU^*=\Delta_N$ for every $N$ and every unitary commuting with $\sigma$. Extended logarithms allow zero probabilities and infinite limiting rate. The event sequence is chosen after the scheme and both states; covariance is not assumed. This realizes the local exponent through stabilizer-invariant events.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 31, Lemma 5.3 / (168)-(170)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.31-32, Lemma 5.3, (168)-(170): the Borel events may depend on
E,rho,sigma; no covariance premise is imposed. Extended logarithms preserve
infinite rates and zero probabilities. The intermediate assertion (173) for
arbitrary closed balls is not assumed. -/
theorem invariant_local_events {d : ℕ} (hd : 0 < d)
    (E : Scheme d (DensityOutcome d)) (I : DensityOutcome d → DensityOutcome d → ℝ≥0∞)
    (hI : SchemeLDP E FullTarget I) (rho sigma : DensityOutcome d) :
    ∃ B : ℕ → Set (DensityOutcome d), (∀ k, MeasurableSet (B k)) ∧
      Tendsto (fun k => E.law k sigma (B k)) atTop (nhds 1) ∧
      Tendsto (fun k => -scaledLog k (E.law k rho (B k))) atTop (nhds (I rho sigma : EReal)) ∧
      ∀ k (U : Matrix.unitaryGroup (Fin d) ℂ),
        (U : Matrix (Fin d) (Fin d) ℂ) * sigma.val = sigma.val * (U : Matrix (Fin d) (Fin d) ℂ) → conjugateState U '' B k = B k := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
