-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P29_trace_net_reduced_error_probability
-- name    : QAlgorithms.Papers.Independent.Extend50.P29.trace_net_reduced_error_probability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:15:24.494299+00:00
-- url     : https://prove2.me/theorems/ddfcd4eb-5050-40a9-b86f-b83439b5a187
-- title:
--   Appendix B, Lemma 2: trace-norm net controls reduced-state operator error
-- statement:
--   Let $G$ be finite, $d=|G|\ge1$, and $n\ge2$. Sample $\Psi=M\phi$ from the invariant-subspace Haar law of Appendix C. For a fixed two-register density matrix $\sigma$ define
--   $$P_{\delta,\sigma}=\Pr\left[\left|\operatorname{Tr}\!\left(\sigma(\Psi_{01}-I/d^2)\right)\right|\ge\delta/d^2\right],\qquad P_\delta=\sup_\sigma P_{\delta,\sigma}.$$
--   The density-matrix test is chosen before sampling. For $0<\alpha\le\epsilon$,
--   $$\Pr\left[\|\Psi_{01}-I/d^2\|_{\rm op}\le\frac{\epsilon}{3d^2}\right]\ge1-P_{(\epsilon-\alpha)/3}\left(\frac{15d^2}{\alpha}\right)^{2d^2}.$$
--   This converts a bound for fixed tests into an operator-error probability bound. There is no upper bound on $\epsilon$. The positive net-radius requirement corrects the printed inclusion of $\alpha=0$; the source's formula is undefined there.
-- source:
--   Error Correction of Quantum Reference Frame Information, arXiv:1709.04471v1, PDF p. 12, Appendix B, Lemma 2: trace-norm net controls reduced-state operator error

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P29

noncomputable section

open MeasureTheory MeasureTheory.Measure

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P29

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt rectAct)

open QAlgorithms.Papers.Independent.Support21.P09 (groupLeftRegular)

/-- PDF p.12, Lemma 2: trace-norm net bound, with positive net radius.
Printed alpha=0 is excluded because that finite-net formula divides by alpha;
epsilon has no upper bound. Here n=r+2. -/
theorem trace_net_reduced_error_probability
    (G : Type) [Group G] [Fintype G] (r : ℕ)
    (α ε : ℝ) (hα : 0 < α) (hαε : α ≤ ε) :
    1 - worstTestTail G r ((ε - α) / 3) *
      (15 * (Fintype.card G : ℝ) ^ 2 / α) ^ (2 * Fintype.card G ^ 2) ≤
    ((invariantSampleLaw G (r + 2)) {φ |
      specNorm (pairMarginal (randomInvariant (r + 2) φ) - pairMixed G) ≤
        ε / (3 * (Fintype.card G : ℝ) ^ 2)}).toReal := by sorry

end QAlgorithms.Papers.Independent.Extend50.P29

end
