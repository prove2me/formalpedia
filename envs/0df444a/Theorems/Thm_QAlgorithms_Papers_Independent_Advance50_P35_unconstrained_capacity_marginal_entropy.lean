-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P35_unconstrained_capacity_marginal_entropy
-- name    : QAlgorithms.Papers.Independent.Advance50.P35.unconstrained_capacity_marginal_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:43:04.643745+00:00
-- url     : https://prove2.me/theorems/55e720ce-aa7a-4e07-a679-409eb31c340f
-- title:
--   Unconstrained capacity equals the marginal entropy
-- statement:
--   Let $\Phi=\{\phi_x,p_x\}_{x=0}^{k-1}$ be a finite nonempty ensemble of pairwise distinct CPTP channels on a common nonzero Hilbert space, with fixed nonnegative probabilities summing to one. Inputs are normalized positive trace-class operators on the full Hilbert spaces; the reference Hilbert space can be any nonzero Hilbert space. Use identical transmitters across different cells and arbitrary collective output measurements. All logarithms are base two and $0\log 0=0$. Let $C(\Phi)$ be the supremum of the conditional Holevo information over every normalized transmitter, every finite $s\geq1$, and every $r\geq0$. Let $V_s$ be the supremum restricted to pure unassisted $s$-signal inputs. Then
--
--   $$C(\Phi)=H(X)=-\sum_xp_x\log_2p_x,\qquad\lim_{s\to\infty}V_s=H(X).$$
--
--   Thus references do not enlarge the unconstrained optimal value. The assertion includes a singleton alphabet, when both sides are zero, and makes no finite-$s$ attainment claim.
-- source:
--   Quantum Reading Capacity, arXiv:1107.3500v1, PDF p. 9, §V Eqs.(47)–(48), Appendix A.2: unconstrained capacity equals marginal entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P35

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsBarycenter tensorApply traceSize)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedRelativeEntropyNats binaryEntropyBits)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix coherentCoefficient)

open QAlgorithms.Papers.Independent.Support50.P20 (IsBinaryEffect)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.8--9, (47)--(48), Appendix A.2, pp.14--15: no shared probe or
pair-independent fidelity is assumed. Finite-s attainment is not asserted. -/
theorem unconstrained_capacity_marginal_entropy {I A : Type} [Nonempty I] [Nonempty A]
    {k : ℕ} (M : Memory I k) :
    unconstrainedCapacity M A = ENNReal.ofReal (memoryEntropy M) ∧
      Tendsto (pureUnassistedValue M) atTop (𝓝 (ENNReal.ofReal (memoryEntropy M))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P35

end
