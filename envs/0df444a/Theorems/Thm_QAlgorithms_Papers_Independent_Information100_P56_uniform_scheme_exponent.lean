-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_uniform_scheme_exponent
-- name    : QAlgorithms.Papers.Independent.Information100.P56.uniform_scheme_exponent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:22:43.588301+00:00
-- url     : https://prove2.me/theorems/ffab39e2-0029-4f0e-9f79-6a76298d259e
-- title:
--   Section V F, Eq.(43): explicit uniform-scheme leakage exponent
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. Let $G$ be a finite group. For $R=B,E$, let $U_R$ be a possibly projective unitary representation and $W_R(g)=U_R(g)\rho_RU_R(g)^\dagger$ for a density seed $\rho_R$. Write $\rho_R(P)=\sum_gP(g)W_R(g)$ and $\Delta(P)=H(\rho_B(P))-H(\rho_E(P))$. A code of length $N\ge1$ maps a uniform index in a set of size $K=ML$ to a word in $G^N$. A finite nonempty balanced universal$_2$ family hashes these indices onto $M$ messages, with every fiber of size $L\ge1$. Its public seed is independent and uniform. To send a uniform secret message, draw uniformly within its hash fiber and independently randomize each channel input by noise with law $P_1$. The induced Eve states are $\omega_v=\rho_E(L_vP_1)$; $\delta_N^E$ denotes full trace-norm leakage, without a factor $1/2$. Assume $P_3=P_u$ and Eve's representation is multiplicity free. Put $\tau=\rho_E(P_1)$ and let $T_{1+t}$ be the minimum over the invariant probability-weight states $\sigma(P_J)$ of $\operatorname{Tr}[(\tau^{1/2}\sigma(P_J)^{-t/(1+t)}\tau^{1/2})^{1+t}]$, with infinity on support violations. For every $0<t\le1$,
--
--   $$\mathbb E_F\delta_N^E\le2^{(1-t)/(1+t)}\exp\!\left(-\frac{tN\rho_{{\rm sac},N}}{1+t}\right)T_{1+t}^{N/(1+t)}.$$
--
--   The minimum over $t\in[0,1]$ also bounds leakage, with endpoint value $2$ at $t=0$. This is valid for arbitrary codeword compositions.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 13, Section V F, Eq.(43): explicit uniform-scheme leakage exponent

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Section V F, p.13, Eq.(43): arbitrary code and balanced universal hashing;
minimum over t includes t=0 with endpoint value 2, and exponent N/(1+t). -/
theorem uniform_scheme_exponent
    {G E J : Type*} [Group G] [Fintype G] [Fintype E] [DecidableEq E] [Nonempty E]
    [Fintype J] [Nonempty J]
    (UE : ProjectiveRep G E) (rhoE : Matrix E E ℂ) (hE : QAlgorithms.IsDensityMatrix rhoE)
    (P1 : G → ℝ) (h1 : IsLaw P1) (d : J → ℕ)
    (R : (j : J) → ProjectiveRep G (Fin (d j)))
    (T : (j : J) → Matrix E (Fin (d j) × Fin 1) ℂ)
    (hdec : IsIsotypic UE d (fun _ => 1) R T)
    (N K M L : ℕ) (hN : 1 ≤ N) (H : BalancedHash K M L)
    (phi : Fin K → Fin N → G) :
    let tau := average (orbit UE rhoE) P1
    let bound := uniformExponent d T tau N L
    let leakage := expectedLeakage H phi (induced (orbit UE rhoE) P1)
    (∀ t ∈ Set.Icc (0 : ℝ) 1, leakage ≤ bound t) ∧
    (∃ t ∈ Set.Icc (0 : ℝ) 1, leakage ≤ bound t ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, bound t ≤ bound s) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
