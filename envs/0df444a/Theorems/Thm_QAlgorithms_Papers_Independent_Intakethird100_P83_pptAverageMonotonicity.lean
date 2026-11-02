-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P83_pptAverageMonotonicity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P83.pptAverageMonotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:10:38.863635+00:00
-- url     : https://prove2.me/theorems/f3a27b72-cd05-4d07-963c-5a295b6f6682
-- title:
--   Monotonicity on average under PPT instruments
-- statement:
--   Let $\rho$ be a normalized state on finite nonzero local spaces $A:B$. Let $(\mathcal N_i)_{i\in I}$ be a discrete PPT instrument with possibly different finite output spaces $A':B'$. Each branch is completely positive and trace nonincreasing, each map $T_{B'}\circ\mathcal N_i\circ T_B$ is completely positive, and the branch maps sum unconditionally on every operator to a trace-preserving channel. Set $p_i=\operatorname{Tr}\mathcal N_i(\rho)$ and, only when $p_i>0$, set $\rho_i=\mathcal N_i(\rho)/p_i$. The average below is unconditionally summable, with a zero summand when $p_i=0$, and
--
--   $$0\le E_W(\rho),\qquad \sum_{i\in I}p_iE_W(\rho_i)\le E_W(\rho).$$
--
--   This includes finite and countable outcome sets. LOCC instruments obey the same inequality because they are PPT instruments by inclusion (1).
-- source:
--   Improved Semidefinite Programming Upper Bound on Distillable Entanglement, arXiv:1601.07940v4, PDF p. 3, Theorem 3: monotonicity on average under PPT and LOCC

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P83

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P83

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

variable {A B C D : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Theorem 3, PDF p.3, expanding (6) on p.2. A PPT instrument includes
all LOCC instruments by inclusion (1). The outcome sum is unconditional,
including zero-probability branches, and output dimensions may differ from input. -/
theorem pptAverageMonotonicity [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    {O : Type*} (N : O → Matrix (A × B) (A × B) ℂ → Matrix (C × D) (C × D) ℂ)
    (hN : PPTInstrument N) (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) :
    0 ≤ entanglementW rho ∧
    ∃ s : ℝ, HasSum (fun i => branchContribution (N i) rho) s ∧ s ≤ entanglementW rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P83

end
