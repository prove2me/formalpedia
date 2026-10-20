-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_communication_sep
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.communication_sep
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:57:10.929933+00:00
-- url     : https://prove2.me/theorems/b5b5c10e-1676-4c4c-a288-8fc4576b7bdf
-- title:
--   SEP-assisted one-shot capacity and simulation cost
-- statement:
--   Let $E$ be a finite-dimensional CPTP transmission channel and $0\le\epsilon<1$. All target dimensions $d$ are positive integers. The operational one-shot capacity $Q^\epsilon$ maximizes $\log_2d$ over deterministic free superchannels converting $E$ to $\operatorname{id}_d$ with squared worst-case reference-assisted fidelity at least $1-\epsilon$. The simulation cost $C^\epsilon$ minimizes the same rate for the reverse conversion. The allowed fibre consists of all CPTP channels.
--
--   Free transmission channels have separable normalized Choi states across input:output, and the free codes are all physical deterministic superchannels preserving this family.
--
--   Writing $R_H^\epsilon$ for the corresponding ordinary testing resource and $R_s^\epsilon$ for fidelity-smoothed standard robustness,
--   $$Q^\epsilon(E)=\log_2\lfloor R_H^\epsilon(E)\rfloor,\qquad C^\epsilon(E)=\log_2\lceil R_s^\epsilon(E)\rceil.$$
--   Both optimizing dimensions and physical codes exist. Rates use extended values before logarithms when necessary; infinity is never converted to real zero.
--
--   These identities characterize both one-shot communication tasks.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 4, SEP-assisted one-shot capacity and simulation cost

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- SEP-assisted communication application, PDF p.4: both one-shot rates,
positive integer target dimensions, log base two and actual optimal codes.
The cost equality recovers cited Ref.[41]. Error one is excluded because
capacity is unbounded there and admits no finite maximizing dimension. -/
theorem communication_sep {p : Port} (E : ChannelChoi p) (hE : CPTP E)
    (e : ℝ) (he : 0 ≤ e) (he1 : e < 1) :
    let O := communicationTheory .sep
    assistedOneShotCapacity O E e = log2Resource (integerFloor 1 (testing O E e)) ∧
    simulationCost O E e = log2Resource
      (integerCeiling 1 (smooth O (standard O) e E)) ∧ RateAttainment O E e := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
