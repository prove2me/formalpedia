-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P32_bipartite_entanglement_rates
-- name    : QAlgorithms.Papers.Independent.Dependency50.P32.bipartite_entanglement_rates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:02:48.683701+00:00
-- url     : https://prove2.me/theorems/b8d09534-f587-487b-9dd9-d06dc2ea9b37
-- title:
--   Bipartite SEP and PPT entanglement rates
-- statement:
--   Let $E:A_{\rm in}B_{\rm in}\to A_{\rm out}B_{\rm out}$ be a CPTP channel in strictly positive finite dimensions and $0\le\epsilon<1$. The reference is preparation of the rank-$d$ maximally entangled state for a positive integer $d$. Operational distillable entanglement and entanglement cost maximize/minimize $\log_2d$ over physical deterministic free superchannels with squared worst-case conversion fidelity at least $1-\epsilon$. For SEP channels, the Choi partition is $(A_{\rm in}A_{\rm out}):(B_{\rm in}B_{\rm out})$; PPT uses positive partial transpose across the same party partition. For the respective maximal preserving superchannel families,
--   $$
--   \begin{aligned}
--   d_{E,\rm SEP}^\epsilon(E)&=\log_2\lfloor R_{H,\mathcal O_{\rm SEP}}^\epsilon(E)\rfloor,&
--   c_{E,\rm SEP}^\epsilon(E)&=\log_2\lceil R_{s,\mathcal O_{\rm SEP}}^\epsilon(E)\rceil,\\
--   d_{E,\rm PPT}^\epsilon(E)&=\log_2\lfloor R_{H,\mathcal O_{\rm PPT}}^\epsilon(E)\rfloor,&
--   c_{E,\rm PPT}^\epsilon(E)&=\log_2\lceil R_{s,\mathcal O_{\rm PPT}}^\epsilon(E)\rceil.
--   \end{aligned}
--   $$
--   All four optimizations have attaining dimensions and physical codes. Hypothesis testing is ordinary and robustness is standard, smoothed within all CPTP channels.
--
--   These are channel entanglement specializations using entangled preparations, not the transmission-channel partition or identity-channel reference of Eq.(4).
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, PDF p. 14, Bipartite SEP and PPT entanglement rates

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- Eq.(E3) and following paragraph, PDF p.14: all FOUR SEP/PPT channel
entanglement rate identities, with positive target dimensions and optimal codes. -/
theorem bipartite_entanglement_rates (s : Split) (E : ChannelChoi (bipartitePort s)) (hE : CPTP E)
    (e : ℝ) (he : 0 ≤ e) (he1 : e < 1) :
    let S := bipartiteTheory false
    let P := bipartiteTheory true
    entanglementDistillation S E e = log2Resource (integerFloor 1 (testing S E e)) ∧
    entanglementCost S E e = log2Resource (integerCeiling 1 (smooth S (standard S) e E)) ∧
    entanglementDistillation P E e = log2Resource (integerFloor 1 (testing P E e)) ∧
    entanglementCost P E e = log2Resource (integerCeiling 1 (smooth P (standard P) e E)) ∧
    EntanglementAttainment S E e ∧ EntanglementAttainment P E e := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P32

end
