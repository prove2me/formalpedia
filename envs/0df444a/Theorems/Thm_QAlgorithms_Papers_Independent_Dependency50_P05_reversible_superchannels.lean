-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_reversible_superchannels
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.reversible_superchannels
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T07:51:17.876982+00:00
-- url     : https://prove2.me/theorems/1937409f-b321-4f81-981c-90536c623dc5
-- title:
--   Reversible superchannels are unitary pre/post processing
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. Assume $d_{A_0}=d_{B_0}$ and $d_{A_1}=d_{B_1}$. If $\Theta$ has a two-sided inverse that is itself a superchannel, then there are unitary channels $\mathcal U_{\rm pre}:B_0\to A_0$ and $\mathcal U_{\rm post}:A_1\to B_1$ such that, for every complex-linear map $\Phi$,
--   $$\Theta[\Phi]=\mathcal U_{\rm post}\circ\Phi\circ\mathcal U_{\rm pre}.$$
--   This characterizes the reversible transformations used in the paper's noise model.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 8, Sec. III-A, Eq.(38)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF p.8, Eq.(38): two-sided physical reversibility forces unitary
pre/post processing on all maps. Equal dimensions are imposed separately on input/output. -/
theorem reversible_superchannels {A B : System} (hin : A.input = B.input)
    (hout : A.output = B.output) (T : Supermap A B) (hT : IsReversible T) :
    ∃ (P : Matrix (In A) (In B) ℂ) (Q : Matrix (Out B) (Out A) ℂ),
      UnitaryBetween P ∧ UnitaryBetween Q ∧ ∀ X, T X = sandwich P Q X := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
