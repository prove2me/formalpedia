-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_qc_reduction
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.qc_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:25:23.703057+00:00
-- url     : https://prove2.me/theorems/b97d2026-55bf-41c9-858f-b971725c9abe
-- title:
--   Quantum-classical restriction of the POVM fidelity optimization
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   The maximum invariant-state fidelity for the measurement Choi density equals an attained maximum over block-diagonal QC densities Σx σ̃x⊗|x⟩⟨x| with σ̃x PSD, total trace 1 and σ̃πg(x)=Ad(conjugate(Ug))(σ̃x) for every g,x.
--
--   $$
--   \max_{\sigma\in\mathrm{Sym}_G}F(\Phi^{\mathcal M},\sigma)=\max_{\substack{\sigma\in\mathrm{Sym}_G\\\sigma=\sum_xb_x\otimes|x\rangle\langle x|}}F(\Phi^{\mathcal M},\sigma),\quad b_x\succeq0,\quad\sum_x\operatorname{Tr}b_x=1.
--   $$
--
--   The formula gives the exact characterization or operational specialization described in the cited result.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 17, Quantum-classical restriction of the POVM fidelity optimization

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P47

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

variable {G S R P T A B C D R2 S2 : Type*}

variable [Fintype G] [Group G] [DecidableEq G]

variable [Fintype S] [DecidableEq S] [Nonempty S]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype P] [DecidableEq P] [Nonempty P]

variable [Fintype T] [DecidableEq T] [Nonempty T]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

variable [Fintype R2] [DecidableEq R2] [Nonempty R2]

variable [Fintype S2] [DecidableEq S2] [Nonempty S2]

/-- PDF p.17: the POVM optimum can be attained on quantum-classical states.
Each block is PSD; individual block traces need not equal one. -/
theorem qc_reduction [Nonempty S] {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (U : G → Matrix.unitaryGroup S ℂ) (hU : IsProjectiveUnitaryLift U)
    (pi : G →* Equiv.Perm X) (L : X → Mat S) (hL : IsPOVM L) :
    ∃ v, IsGreatest (symmetryFidelityValues (normalizedChoi (povmOutcomeChannel L))
      (Sym (choiFamily (fun g => (U g : Mat S)) (fun g => outcomeMatrix (pi g))))) v ∧
    IsGreatest {w | ∃ b : X → Mat S, (∀ x, (b x).PosSemidef) ∧
      (∑ x, (b x).trace = 1) ∧
      Sym (choiFamily (fun g => (U g : Mat S)) (fun g => outcomeMatrix (pi g))) (qcBlockMatrix b) ∧
      w = rootFidelity (normalizedChoi (povmOutcomeChannel L)) (qcBlockMatrix b) ^ 2} v := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
