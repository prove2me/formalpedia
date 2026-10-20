-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_translation_invariance
-- name    : QAlgorithms.Papers.Independent.Information100.P56.translation_invariance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:14:31.036299+00:00
-- url     : https://prove2.me/theorems/80498579-a63f-4c8e-8d5c-b692e612bdc2
-- title:
--   Lemma II.3: translation invariance
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. Let $G$ be a finite group. For $R=B,E$, let $U_R$ be a possibly projective unitary representation and $W_R(g)=U_R(g)\rho_RU_R(g)^\dagger$ for a density seed $\rho_R$. Write $\rho_R(P)=\sum_gP(g)W_R(g)$ and $\Delta(P)=H(\rho_B(P))-H(\rho_E(P))$. For a probability law $P$ and $v\in G$, set $(L_vP)(x)=P(v^{-1}x)$. Then
--
--   $$\rho_R(L_vP)=U_R(v)\rho_R(P)U_R(v)^\dagger\quad(R=B,E),\qquad\Delta(L_vP)=\Delta(P).$$
--
--   Thus conditional entropies of translated noise do not depend on the translation.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 5, Lemma II.3: translation invariance

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Lemma II.3, p.5: covariance of both averaged states and invariance of Delta. -/
theorem translation_invariance
    {G B E : Type*} [Group G] [Fintype G] [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E] [Nonempty B] [Nonempty E]
    (UB : ProjectiveRep G B) (UE : ProjectiveRep G E)
    (rhoB : Matrix B B ℂ) (rhoE : Matrix E E ℂ)
    (hB : QAlgorithms.IsDensityMatrix rhoB) (hE : QAlgorithms.IsDensityMatrix rhoE)
    (P : G → ℝ) (hP : IsLaw P) (v : G) :
    average (orbit UB rhoB) (translate v P) =
      (UB.unitary v : Matrix B B ℂ) * average (orbit UB rhoB) P *
        (UB.unitary v : Matrix B B ℂ)ᴴ ∧
    average (orbit UE rhoE) (translate v P) =
      (UE.unitary v : Matrix E E ℂ) * average (orbit UE rhoE) P *
        (UE.unitary v : Matrix E E ℂ)ᴴ ∧
    delta (orbit UB rhoB) (orbit UE rhoE) (translate v P) =
      delta (orbit UB rhoB) (orbit UE rhoE) P := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
