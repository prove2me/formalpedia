-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P27_accessible_bound2
-- name    : QAlgorithms.Papers.Independent.Support50.P27.accessible_bound2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:11:37.664024+00:00
-- url     : https://prove2.me/theorems/dee7a7aa-9bdf-4ee4-a325-d3076f32faff
-- title:
--   §5.1 Bound 2: improved accessible-information bound
-- statement:
--   Use normalized finite conditional QKD output data with public length distribution $p_m$ and maximum supported length $L$. For each $m$, use the uniform diagonal ensemble $\mathcal F_m=\{2^{-m},\rho_{E,k,k}\}_k$ and its mean $\bar\rho_m$. Let $\rho_{\mathrm{qi1}}$ retain these conditional diagonal Eve states and let $\rho_{\mathrm{qi2}}$ replace them by $\bar\rho_m$, in both cases using equal uniform keys with length weight $p_m$. Choose normalized representatives for every null conditional outcome. If $\mu_2\ge0$ and $\sum_mp_mI_{\mathrm{acc}}(\mathcal F_m)\le\mu_2$, with information in bits, then
--
--   $$
--   \lVert\rho_{\mathrm{qi1}}-\rho_{\mathrm{qi2}}\rVert_1
--   \le\sum_mp_m2^{m/2+1}\sqrt{I_{\mathrm{acc}}(\mathcal F_m)}
--   \le2^{L/2+1}\sqrt{\mu_2}.
--   $$
--
--   Consequently the Eq. (15) privacy defect obeys
--
--   $$
--   \frac12\sum_mp_m2^{-m}\sum_k\lVert\rho_{E,k,k}-\bar\rho_m\rVert_1
--   \le2^{L/2}\sqrt{\mu_2}.
--   $$
--
--   This reduces the length overhead in Bound 1. The theorem is the finite inequality; decay for growing families requires an appropriate rate restriction. The information premise concerns $\mathcal F_m$, rather than the generally different actual key-pair prior.
-- source:
--   The Universal Composable Security of Quantum Key Distribution, arXiv:quant-ph/0409078v1, PDF p. 12, §5.1 Bound 2: improved accessible-information bound

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P27

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P07
  (CQData ensembleMean ensembleInformation accessibleInformation)

open QAlgorithms.Papers.Independent.Dependency50.P24 (Key)

open QAlgorithms.Papers.Independent.Dependency50.P47 (cqMatrix)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF pp.12--13, Section 5.1, Bound 2: full hybrid trace norm bounded by
2^(max(m)/2+1) sqrt(mu2), written as 2 sqrt(2^max(m)) sqrt(mu2).
The source's false printed Lemma 2 is NOT a hypothesis. The finite bound
survives via label-versus-mean Pinsker; no rate-uniform decay or conversion
from the actual-prior privacy condition is asserted. -/
theorem accessible_bound2 {L : ℕ} {E : Type} [Fintype E] [Nonempty E]
    (D : KeyData L E) (mu2 : ℝ) (hmu2 : 0 ≤ mu2)
    (hprivacy : diagonalAccessible D ≤ mu2) :
    traceNorm (firstHybrid D - secondHybrid D) ≤
      (∑ m, D.lengthProb m * (2 * Real.sqrt ((2 : ℝ) ^ m.val)) *
        Real.sqrt (accessibleInformation (diagonalEnsemble D m))) ∧
    (∑ m, D.lengthProb m * (2 * Real.sqrt ((2 : ℝ) ^ m.val)) *
        Real.sqrt (accessibleInformation (diagonalEnsemble D m))) ≤
      2 * Real.sqrt ((2 : ℝ) ^ maxKeyLength D) * Real.sqrt mu2 ∧
    composablePrivacy D ≤
      Real.sqrt ((2 : ℝ) ^ maxKeyLength D) * Real.sqrt mu2 := by sorry

end QAlgorithms.Papers.Independent.Support50.P27

end
