-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_uniform_orbit_renyi
-- name    : QAlgorithms.Papers.Independent.Information100.P56.uniform_orbit_renyi
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:20:56.858997+00:00
-- url     : https://prove2.me/theorems/fd5b5c1f-9f94-400a-ad90-7d4370517a6f
-- title:
--   Lemma V.5: uniform orbit Renyi bound for arbitrary codes
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. Let $G$ be a finite group. For $R=B,E$, let $U_R$ be a possibly projective unitary representation and $W_R(g)=U_R(g)\rho_RU_R(g)^\dagger$ for a density seed $\rho_R$. Write $\rho_R(P)=\sum_gP(g)W_R(g)$ and $\Delta(P)=H(\rho_B(P))-H(\rho_E(P))$. A code of length $N\ge1$ maps a uniform index in a set of size $K=ML$ to a word in $G^N$. A finite nonempty balanced universal$_2$ family hashes these indices onto $M$ messages, with every fiber of size $L\ge1$. Its public seed is independent and uniform. To send a uniform secret message, draw uniformly within its hash fiber and independently randomize each channel input by noise with law $P_1$. The induced Eve states are $\omega_v=\rho_E(L_vP_1)$; $\delta_N^E$ denotes full trace-norm leakage, without a factor $1/2$. For uniform outer randomization $P_3=P_u$, every code and every $\alpha>1$ satisfy
--
--   $$I_\alpha(M';E^N)\le N I_\alpha(A;E),$$
--
--   where $\rho_{AE}=|G|^{-1}\sum_x|x\rangle\langle x|\otimes U_E(x)\rho_E(P_1)U_E(x)^\dagger$. No composition condition is imposed. This bounds arbitrary code ensembles by the single-copy uniform orbit.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 11, Lemma V.5: uniform orbit Renyi bound for arbitrary codes

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Lemma V.5, pp.11–12: arbitrary codes under uniform orbit randomization,
with every alpha>1 and no constant-composition hypothesis. -/
theorem uniform_orbit_renyi
    {G E : Type*} [Group G] [Fintype G] [Fintype E] [DecidableEq E] [Nonempty E]
    (UE : ProjectiveRep G E) (rhoE : Matrix E E ℂ) (hE : QAlgorithms.IsDensityMatrix rhoE)
    (P1 : G → ℝ) (h1 : IsLaw P1) (N K : ℕ) (hN : 1 ≤ N) (hK : 0 < K)
    (phi : Fin K → Fin N → G) (alpha : ℝ) (ha : 1 < alpha) :
    let omega := induced (orbit UE rhoE) P1
    renyiInfo alpha uniform (fun k => productOutput N omega (phi k)) ≤
      (N : ENNReal) * renyiInfo alpha uniform omega := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
