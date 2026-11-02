-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P74_damping_phase_state
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P74.damping_phase_state
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:13:51.166087+00:00
-- url     : https://prove2.me/theorems/b7c67add-ed03-44e4-b279-fad43c3601d8
-- title:
--   Exact amplitude-damping phase output matrix
-- statement:
--   For $0\le\eta\le1$, let $\mathcal N_\eta$ be the qubit amplitude-damping channel with Kraus operators $\sqrt{1-\eta}|0\rangle\langle1|$ and $|0\rangle\langle0|+\sqrt\eta|1\rangle\langle1|$. Let $|\Phi\rangle=(|00\rangle+|11\rangle)/\sqrt2$, with reference $C$ first, and modulate $C$ by $Z^x$ for $x\in\{0,1\}$. In the ordered basis $|00\rangle,|01\rangle,|10\rangle,|11\rangle$,
--
--   $$
--   (\mathrm{id}_C\otimes\mathcal N_\eta)(Z_C^x|\Phi\rangle\langle\Phi|Z_C^x)
--   =\begin{pmatrix}
--   \frac12&0&0&\frac{(-1)^x\sqrt\eta}{2}\\
--   0&0&0&0\\
--   0&0&\frac{1-\eta}{2}&0\\
--   \frac{(-1)^x\sqrt\eta}{2}&0&0&\frac\eta2
--   \end{pmatrix}.
--   $$
--
--   This gives an exact symbolic phase-channel state, without inferring a numerical parameter interval from Figure 2.
-- source:
--   Polar codes for private classical communication, arXiv:1203.5794v1, PDF p. 11, Appendix C.C, unnumbered: explicit phase-channel output matrices

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P74

namespace QAlgorithms.Papers.Independent.Intakethird100.P74

open QAlgorithms

open scoped ComplexConjugate Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {B E S1 S2 : Type}

variable [Fintype B] [Fintype E] [Fintype S1] [Fintype S2]

variable [DecidableEq B] [DecidableEq E] [DecidableEq S1] [DecidableEq S2]

/-- PDF pp.10–11, Appendix C.C: the normalized symbolic phase output matrix, in
C-first computational order. The undefined gamma in an intermediate line is bypassed
using the printed Kraus operators and the final eta-only formula. No numerical key-rate
interval is inferred from this exact state identity. -/
theorem damping_phase_state (eta : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1) (x : Bool) :
    dampingPhaseOutput eta x = Matrix.of (fun p q =>
      dampingPhaseMatrix eta x (cbIndex p) (cbIndex q)) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P74
