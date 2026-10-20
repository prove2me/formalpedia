-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_communication_ns
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.communication_ns
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:58:55.1179+00:00
-- url     : https://prove2.me/theorems/b868f232-fb1c-4e91-85bb-85a5d229a36c
-- title:
--   NS-assisted rates with attainable-square rounding
-- statement:
--   Let $E$ be a finite-dimensional CPTP transmission channel and $0\le\epsilon<1$. All target dimensions $d$ are positive integers. The operational one-shot capacity $Q^\epsilon$ maximizes $\log_2d$ over deterministic free superchannels converting $E$ to $\operatorname{id}_d$ with squared worst-case reference-assisted fidelity at least $1-\epsilon$. The simulation cost $C^\epsilon$ minimizes the same rate for the reverse conversion. The allowed fibre consists of all CPTP channels.
--
--   Free channels are all replacement channels $X\mapsto\operatorname{Tr}(X)\sigma$ with $\sigma$ a density matrix. Codes are maximal physical replacement-preserving deterministic superchannels. Let $\lfloor x\rfloor_{\square}=\sup\{d^2:d\in\mathbb N_{>0},d^2\le x\}$ and $\lceil x\rceil_{\square}=\inf\{d^2:d\in\mathbb N_{>0},x\le d^2\}$. Then
--   $$
--   Q^\epsilon(E)=\tfrac12\log_2\lfloor R_{H,\operatorname{aff}(\mathcal O_R)}^\epsilon(E)\rfloor_{\square},\qquad
--   C^\epsilon(E)=\tfrac12\log_2\lceil R_{\max,\mathcal O_R}^\epsilon(E)\rceil_{\square}.
--   $$
--   Both dimensions and codes are attained. These are equivalently integer rounding after square roots.
--
--   The reference rounding follows Eq.(4), the target resource value $d^2$, and (C3). A bare integer floor or ceiling inside the half logarithm would give rates that need not equal the logarithm of an integer dimension.
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 4, NS-assisted rates with attainable-square rounding

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- NS-assisted rates, PDF pp.4,12. Source correction: the bare floor/ceiling
on p.4 is read as reference rounding over {d^2:d>=1}, as forced by Eq.(4)
and (C3). At R=3 this gives target dimension 1, not a spurious sqrt(3).
Both ordinary/affine distinctions and code attainment are retained. -/
theorem communication_ns {p : Port} (E : ChannelChoi p) (hE : CPTP E)
    (e : ℝ) (he : 0 ≤ e) (he1 : e < 1) :
    let O := communicationTheory .ns
    assistedOneShotCapacity O E e = log2Resource (integerFloor 2 (testingAffine O E e)) / 2 ∧
    simulationCost O E e = log2Resource
      (integerCeiling 2 (smooth O (maximal O) e E)) / 2 ∧ RateAttainment O E e := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
