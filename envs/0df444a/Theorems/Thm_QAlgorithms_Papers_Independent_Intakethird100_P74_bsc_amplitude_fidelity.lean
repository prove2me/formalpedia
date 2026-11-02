-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P74_bsc_amplitude_fidelity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P74.bsc_amplitude_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:11:52.473206+00:00
-- url     : https://prove2.me/theorems/4b406b37-14cf-4601-88a7-a6775321d3cf
-- title:
--   BSC amplitude root fidelity
-- statement:
--   Let $p_B\in[0,1]$ and let Bob's computational-basis signal states be those of a BSC: $\rho_x=(1-p_B)|x\rangle\langle x|+p_B|1-x\rangle\langle1-x|$. With the source's squared-fidelity convention,
--
--   $$
--   \sqrt{F(\rho_0,\rho_1)}=2\sqrt{p_B(1-p_B)}.
--   $$
--
--   This is the classical Bhattacharyya parameter of Bob's amplitude channel. The expression is root fidelity, rather than its square.
-- source:
--   Polar codes for private classical communication, arXiv:1203.5794v1, PDF p. 7, Appendix C.A, unnumbered: amplitude root fidelity of BSC

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P74

namespace QAlgorithms.Papers.Independent.Intakethird100.P74

open QAlgorithms

open scoped ComplexConjugate Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {B E S1 S2 : Type}

variable [Fintype B] [Fintype E] [Fintype S1] [Fintype S2]

variable [DecidableEq B] [DecidableEq E] [DecidableEq S1] [DecidableEq S2]

/-- PDF p.7, Appendix C.A: the amplitude ROOT fidelity, with radical over p(1-p). -/
theorem bsc_amplitude_fidelity (pB : ℝ) (hp0 : 0 ≤ pB) (hp1 : pB ≤ 1) :
    rootFidelity (bscOutput pB false) (bscOutput pB true) =
      2 * Real.sqrt (pB * (1 - pB)) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P74
