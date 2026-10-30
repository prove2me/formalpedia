-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_sdp_bose
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.sdp_bose
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:26:07.798352+00:00
-- url     : https://prove2.me/theorems/6d9bc530-bb55-4191-b33c-bef4a19c49a4
-- title:
--   SDP (142): maximum Bose root fidelity
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation. The set $\mathrm{Sym}_G$ consists of invariant densities; $\mathrm{B\!\text{-}Sym}_G$ consists of densities supported by $\Pi$. The sets $\mathrm{SymExt}_G$ and $\mathrm{BSE}_G$ are their normalized-extension marginal analogues, tracing out precisely the stated reference register.
--
--   The attained maximum of sqrt(F(ρ,τ)) over B-SymG equals the attained maximum Re Tr X subject to [[ρ,X†],[X,τ]] PSD, trace-one PSD σ, and σ=ΠUσΠU. The optimal acceptance probability is the square of this optimum. A nonzero Bose average is required for the maximum; when it vanishes, the SDP is infeasible.
--
--   $$
--   \max_{\sigma\in\mathrm{B\!\text{-}Sym}_G}\sqrt{F(\rho,\sigma)}=\max_{X,\sigma_S}\operatorname{Re}\operatorname{Tr}X,\quad\begin{pmatrix}\rho&X^\dagger\\X&\sigma_S\end{pmatrix}\succeq0,\quad\sigma_S\succeq0,\quad\operatorname{Tr}\sigma_S=1,\quad\sigma_S=\Pi\sigma_S\Pi.
--   $$
--
--   The formula gives the exact characterization or operational specialization described in the cited result. Here $X$ acts on $S$; an extension variable acts on $RS$, and only its $S$ marginal is placed in the lower-right block. The objective is root fidelity, rather than a probability.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 18, SDP (142): maximum Bose root fidelity

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

/-- PDF p.18, (142). Source correction: the Bose problem has an attained
maximum when its projector is nonzero; otherwise the SDP is infeasible. -/
theorem sdp_bose [Nonempty S] (U : G →* Matrix.unitaryGroup S ℂ) (rho : Mat S)
    (hrho : IsDensityMatrix rho) :
    (symmetryControlAverage (fun g => (U g : Mat S)) ≠ 0 → ∃ v,
      IsGreatest (rootValues rho (Bose (symmetryControlAverage (fun g => (U g : Mat S))))) v ∧
      IsGreatest (stateSDP rho (Bose (symmetryControlAverage (fun g => (U g : Mat S))))) v) ∧
    (symmetryControlAverage (fun g => (U g : Mat S)) = 0 →
      stateSDP rho (Bose (symmetryControlAverage (fun g => (U g : Mat S)))) = ∅) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
