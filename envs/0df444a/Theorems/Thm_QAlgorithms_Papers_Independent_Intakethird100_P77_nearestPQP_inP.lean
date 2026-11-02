-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P77_nearestPQP_inP
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P77.nearestPQP_inP
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:17:49.420487+00:00
-- url     : https://prove2.me/theorems/2d9583e2-d3ab-43de-a521-5af6dabbcfca
-- title:
--   Nearest-neighbour PQP matchgate languages lie in deterministic P
-- statement:
--   Let $\mathcal V_{\mathrm{n.n.}}$ consist of languages recognized by effectively uniform nearest-neighbour matchgate circuits on computational-basis inputs and zero workspace, with a single designated output. Require symmetric majority gaps of inverse-exponential size: one polynomial $q$ is selected before all inputs, with $q(n)\ge2$, and acceptance is at least $1/2+2^{-q(|x|)}$ on members and at most $1/2-2^{-q(|x|)}$ on nonmembers. Then
--
--   $$\mathcal V_{\mathrm{n.n.}}\subseteq\mathrm P.$$
--
--   The polynomial exponent makes the source polynomial-padding convention explicit and keeps the condition meaningful at input length zero. The classical characteristic-function machine has worst-case polynomial runtime. This conclusion uses polynomially many strong-simulation accuracy digits to resolve the exponentially small gap.
-- source:
--   Matchgates and classical simulation of quantum circuits, arXiv:0804.4050v2, PDF p. 16, Section 7: nearest-neighbour PQP matchgate languages lie in P

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P77

open QAlgorithms

open QAlgorithms.Complexity (Str)

open QAlgorithms.Papers.Independent.Advance50.P19 (Major CARSystem)

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.16: nearest-neighbour PQP matchgate languages lie in P. Polynomially
many precision digits suffice for the explicitly padded inverse-exponential
gap; no constant bounded-error gap is substituted. Printed: gap 2^(-n).
Changed: one polynomially padded exponent >=2, chosen before all inputs.
Why: the literal zero-length gap is impossible, and the source's simulation
argument only needs polynomially many precision digits. -/
theorem nearestPQP_inP :
    {L : Set Str | InPQPMatchgate 1 L} ⊆ {L : Set Str | InP L} := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P77

end
