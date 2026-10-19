-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_constant_composition_renyi
-- name    : QAlgorithms.Papers.Independent.Information100.P56.constant_composition_renyi
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:18:34.185019+00:00
-- url     : https://prove2.me/theorems/0b4e5350-9a18-42a6-8bef-36d948157cff
-- title:
--   Lemma V.1: constant-composition Renyi leakage bound
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. Let $G$ be a finite group. For $R=B,E$, let $U_R$ be a possibly projective unitary representation and $W_R(g)=U_R(g)\rho_RU_R(g)^\dagger$ for a density seed $\rho_R$. Write $\rho_R(P)=\sum_gP(g)W_R(g)$ and $\Delta(P)=H(\rho_B(P))-H(\rho_E(P))$. A code of length $N\ge1$ maps a uniform index in a set of size $K=ML$ to a word in $G^N$. A finite nonempty balanced universal$_2$ family hashes these indices onto $M$ messages, with every fiber of size $L\ge1$. Its public seed is independent and uniform. To send a uniform secret message, draw uniformly within its hash fiber and independently randomize each channel input by noise with law $P_1$. The induced Eve states are $\omega_v=\rho_E(L_vP_1)$; $\delta_N^E$ denotes full trace-norm leakage, without a factor $1/2$. Fix $P_3$, put $S=\operatorname{supp}P_3$ and $\sigma_E=\sum_vP_3(v)\omega_v$, and define $J_\alpha(Q)=\sum_{v\in S}Q(v)D_\alpha(\omega_v\|\sigma_E)$ using sandwiched Rényi divergence. If every codeword has type $Q_N$ supported on $S$, then, for $1<\alpha\le2$,
--
--   $$I_\alpha(M';E^N)\le N J_\alpha(Q_N).$$
--
--   The comparison state is the fixed $P_3$ average. Its support contains each summand's state, so the divergences are finite.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 9, Lemma V.1: constant-composition Renyi leakage bound

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Lemma V.1, pp.9–10: the fixed comparison state and the actual uniform-index
code ensemble give the constant-composition Renyi bound. -/
theorem constant_composition_renyi
    {G E : Type*} [Group G] [Fintype G] [DecidableEq G]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (UE : ProjectiveRep G E) (rhoE : Matrix E E ℂ) (hE : QAlgorithms.IsDensityMatrix rhoE)
    (P1 P3 Q : G → ℝ) (h1 : IsLaw P1) (h3 : IsLaw P3) (hQ : IsLaw Q)
    (hsupp : ∀ v, P3 v = 0 → Q v = 0)
    (N K : ℕ) (hN : 1 ≤ N) (hK : 0 < K)
    (phi : Fin K → Fin N → G) (htype : HasType phi Q)
    (alpha : ℝ) (ha : 1 < alpha ∧ alpha ≤ 2) :
    let omega := induced (orbit UE rhoE) P1
    renyiInfo alpha uniform (fun k => productOutput N omega (phi k)) ≤
      ENNReal.ofReal ((N : ℝ) * renyiJ alpha P3 Q omega) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
