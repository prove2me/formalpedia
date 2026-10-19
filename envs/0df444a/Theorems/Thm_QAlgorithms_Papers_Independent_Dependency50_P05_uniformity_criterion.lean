-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_uniformity_criterion
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.uniformity_criterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T07:53:56.209605+00:00
-- url     : https://prove2.me/theorems/faa08eff-14fe-4d90-9c10-a6abb9acc34e
-- title:
--   Ordinary uniformity preservation from a Choi marginal
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. Suppose $d_{A_0}=d_{B_0}$ and $d_{A_1}=d_{B_1}$, and let $\Theta$ be a superchannel. Define $N^A(X)=\operatorname{Tr}(X)u^{A_1}$ and similarly $N^B$. Then
--   $$\Theta[N^A]=N^B\quad\Longleftrightarrow\quad J_\Theta^B=I^B.$$
--   This is the ordinary uniform-channel preservation criterion.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 9, Sec. III-C, following Eq.(54)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF p.9, Sec.III-C: ORDINARY uniformity preservation criterion. -/
theorem uniformity_criterion {A B : System} (hin : A.input = B.input)
    (hout : A.output = B.output) (T : Supermap A B) (hT : IsSuperchannel T) :
    PreservesUniformity T ↔ jB T = 1 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
