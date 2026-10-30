-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_sdp_se
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.sdp_se
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:28:32.141979+00:00
-- url     : https://prove2.me/theorems/8e5b2796-593b-495f-ada6-449ce8193797
-- title:
--   SDP (145): maximum SE root fidelity
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation. The set $\mathrm{Sym}_G$ consists of invariant densities; $\mathrm{B\!\text{-}Sym}_G$ consists of densities supported by $\Pi$. The sets $\mathrm{SymExt}_G$ and $\mathrm{BSE}_G$ are their normalized-extension marginal analogues, tracing out precisely the stated reference register.
--
--   The attained maximum of sqrt(F(ρ,τ)) over SymExtG equals the attained maximum Re Tr X subject to [[ρ,X†],[X,τ]] PSD, trace-one PSD ω, and τ=TrRω, ∀g,ω=U(g)ωU(g)†. The optimal acceptance probability is the square of this optimum.
--
--   $$
--   \max_{\sigma\in\mathrm{SymExt}_G}\sqrt{F(\rho,\sigma)}=\max_{X,\omega_{RS}}\operatorname{Re}\operatorname{Tr}X,\quad\begin{pmatrix}\rho&X^\dagger\\X&\operatorname{Tr}_R\omega_{RS}\end{pmatrix}\succeq0,\quad\omega_{RS}\succeq0,\quad\operatorname{Tr}\omega_{RS}=1,\quad\omega_{RS}=U(g)\omega_{RS}U(g)^\dagger\ (\forall g).
--   $$
--
--   The formula gives the exact characterization or operational specialization described in the cited result. Here $X$ acts on $S$; an extension variable acts on $RS$, and only its $S$ marginal is placed in the lower-right block. The objective is root fidelity, rather than a probability.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 18, SDP (145): maximum SE root fidelity

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

/-- PDF p.18, (145): equality of attained root-fidelity and invariant-extension
SDP maxima; the marginal occupies only the lower-right block. -/
theorem sdp_se [Nonempty S] [Nonempty R] (U : G → Matrix.unitaryGroup (R × S) ℂ) (hU : IsProjectiveUnitaryLift U)
    (rho : Mat S) (hrho : IsDensityMatrix rho) :
    ∃ v, IsGreatest (rootValues rho (SE (fun g => (U g : Mat (R × S))))) v ∧
      IsGreatest (extensionSDP rho (Sym (fun g => (U g : Mat (R × S))))) v := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
