-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_covariant_preprocessing
-- name    : QAlgorithms.Papers.Independent.Information100.P56.covariant_preprocessing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:12:44.939314+00:00
-- url     : https://prove2.me/theorems/51e1ffd9-6930-426d-b66a-55d3e1fd0e65
-- title:
--   Theorem IV.1: covariant preprocessing identity and bounds
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. Let $G$ be a finite group. For $R=B,E$, let $U_R$ be a possibly projective unitary representation and $W_R(g)=U_R(g)\rho_RU_R(g)^\dagger$ for a density seed $\rho_R$. Write $\rho_R(P)=\sum_gP(g)W_R(g)$ and $\Delta(P)=H(\rho_B(P))-H(\rho_E(P))$. For independent $V\sim P_3$ and $Z\sim P_1$, send $X=VZ$; thus $P_{VX}(v,x)=P_3(v)P_1(v^{-1}x)$. With $(P_3*P_1)(x)=\sum_vP_3(v)P_1(v^{-1}x)$ and $P_u$ uniform,
--
--   $$I(V;B)-I(V;E)=\Delta(P_3*P_1)-\Delta(P_1),$$
--   $$C^{(1)}\ge\max_{P_1,P_3}[\Delta(P_3*P_1)-\Delta(P_1)]\ge\Delta(P_u)-\min_P\Delta(P).$$
--
--   The extrema are attained. If $P_u$ maximizes $\Delta$, then $C^{(1)}=\Delta(P_u)-\min_P\Delta(P)$; this is a sufficient condition. This identity evaluates the translated-noise encoder exactly.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 6, Theorem IV.1: covariant preprocessing identity and bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Theorem IV.1, pp.6–7: exact preprocessing identity, attained pair optimum,
uniform lower bound, and the source's sufficient equality condition. -/
theorem covariant_preprocessing
    {G B E : Type*} [Group G] [Fintype G] [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E] [Nonempty B] [Nonempty E]
    (UB : ProjectiveRep G B) (UE : ProjectiveRep G E)
    (rhoB : Matrix B B ℂ) (rhoE : Matrix E E ℂ)
    (hB : QAlgorithms.IsDensityMatrix rhoB) (hE : QAlgorithms.IsDensityMatrix rhoE)
    (P1 P3 : G → ℝ) (h1 : IsLaw P1) (h3 : IsLaw P3) :
    let WB := orbit UB rhoB
    let WE := orbit UE rhoE
    let D := delta WB WE
    translatedValue WB WE P1 P3 = D (convolution P3 P1) - D P1 ∧
    ∃ Plo Q1 Q3 : G → ℝ, IsLaw Plo ∧ IsLaw Q1 ∧ IsLaw Q3 ∧
      (∀ P, IsLaw P → D Plo ≤ D P) ∧
      (∀ A B, IsLaw A → IsLaw B →
        D (convolution B A) - D A ≤ D (convolution Q3 Q1) - D Q1) ∧
      D (convolution Q3 Q1) - D Q1 ≤ privateInfo WB WE ∧
      D uniform - D Plo ≤ D (convolution Q3 Q1) - D Q1 ∧
      ((∀ P, IsLaw P → D P ≤ D uniform) → privateInfo WB WE = D uniform - D Plo) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
