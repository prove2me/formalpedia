-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P27_accessible_bound1
-- name    : QAlgorithms.Papers.Independent.Support50.P27.accessible_bound1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:10:52.75117+00:00
-- url     : https://prove2.me/theorems/655adb73-03fe-4b76-ae4b-cb58c3d894ca
-- title:
--   §5.1 Bound 1: first accessible-information bound
-- statement:
--   Fix a finite dimensional Eve register and any fixed-parameter conditional QKD output data. Let $p_m=\Pr(M=m)$, with $p_m\ge0$ and $\sum_mp_m=1$, and let $L=\max\{m:p_m>0\}$. At each length, all conditional key-pair probabilities are normalized and all conditional Eve operators are density operators. Choose arbitrary normalized representatives on null events. Define
--
--   $$
--   \mathcal F_m=\{2^{-m},\rho_{E,k,k}\}_{k\in\{0,1\}^m},\qquad
--   \bar\rho_m=2^{-m}\sum_k\rho_{E,k,k},
--   $$
--
--   and define the hybrid states
--
--   $$
--   \rho_{\mathrm{qi1}}=\sum_{m,k}p_m2^{-m}|k,k\rangle\langle k,k|\otimes\rho_{E,k,k},\qquad
--   \rho_{\mathrm{qi2}}=\sum_{m,k}p_m2^{-m}|k,k\rangle\langle k,k|\otimes\bar\rho_m.
--   $$
--
--   If $\mu_2\ge0$ and $\sum_mp_mI_{\mathrm{acc}}(\mathcal F_m)\le\mu_2$, where information is in bits, then the full trace norm satisfies
--
--   $$
--   \lVert\rho_{\mathrm{qi1}}-\rho_{\mathrm{qi2}}\rVert_1
--   \le\sum_mp_m(2^m+1)^2\sqrt{2\ln2}\sqrt{I_{\mathrm{acc}}(\mathcal F_m)}
--   \le(2^L+1)^2\sqrt{2\ln2}\sqrt{\mu_2}.
--   $$
--
--   This is the finite quantitative bound in the source's uniform-ensemble interpretation. Its exponential length overhead must be absorbed by a separate key-rate restriction before drawing asymptotic conclusions. It does not convert the actual-prior privacy premise of Eq. (4) into the displayed premise.
-- source:
--   The Universal Composable Security of Quantum Key Distribution, arXiv:quant-ph/0409078v1, PDF p. 11, §5.1 Bound 1: first accessible-information bound

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P27

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P07
  (CQData ensembleMean ensembleInformation accessibleInformation)

open QAlgorithms.Papers.Independent.Dependency50.P24 (Key)

open QAlgorithms.Papers.Independent.Dependency50.P47 (cqMatrix)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF pp.11--12, Section 5.1, Bound 1: full hybrid trace norm bounded by
(2^max(m)+1)^2 sqrt(2 ln 2) sqrt(mu2). The hypothesis concerns the explicitly
uniform F_m of the proof. It supplies NO actual-prior conversion from Eq.(4).
The displayed per-length bound is retained; exponential decay needs a rate
restriction and is not asserted for arbitrary key-length families. -/
theorem accessible_bound1 {L : ℕ} {E : Type} [Fintype E] [Nonempty E]
    (D : KeyData L E) (mu2 : ℝ) (hmu2 : 0 ≤ mu2)
    (hprivacy : diagonalAccessible D ≤ mu2) :
    traceNorm (firstHybrid D - secondHybrid D) ≤
      (∑ m, D.lengthProb m * ((2 : ℝ) ^ m.val + 1) ^ 2 *
        Real.sqrt (2 * Real.log 2) *
          Real.sqrt (accessibleInformation (diagonalEnsemble D m))) ∧
    (∑ m, D.lengthProb m * ((2 : ℝ) ^ m.val + 1) ^ 2 *
        Real.sqrt (2 * Real.log 2) *
          Real.sqrt (accessibleInformation (diagonalEnsemble D m))) ≤
      ((2 : ℝ) ^ maxKeyLength D + 1) ^ 2 *
        Real.sqrt (2 * Real.log 2) * Real.sqrt mu2 := by sorry

end QAlgorithms.Papers.Independent.Support50.P27

end
