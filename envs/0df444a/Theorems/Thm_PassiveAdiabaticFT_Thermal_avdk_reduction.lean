-- Prove2me | Theorems.Thm_PassiveAdiabaticFT_Thermal_avdk_reduction
-- name    : PassiveAdiabaticFT.Thermal.avdk_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:19.857845+00:00
-- url     : https://prove2.me/theorems/2fc8564f-a3fb-44ac-8114-6abcea32c443
-- title:
--   Proof of Theorem 3.5, (3.41)–(3.42) — the [AVDK+08] circuit-to-adiabatic reduction
-- statement:
--   There is a constant $C>0$ such that for every $n\ge1$, $T\ge0$, $\varepsilon>0$ and every circuit $\mathcal C$ of $T$ gates on $n$ qubits (each gate a unitary on at most two qubits) there are $N\le C(n+(T+1)/\varepsilon)$ qubits, a duration $0<T'\le C(2+n+T+1/\varepsilon)^C$, two Hamiltonians $K_0=\sum_AK_{0,A}$, $K_1=\sum_AK_{1,A}$ on $N$ qubits whose terms are Hermitian, act on at most $C$ qubits and have operator norm at most $C$ — also after merging the terms of $K_0$ (resp. $K_1$) that have the same support — with $|0^N\rangle$ a ground state of $K_0$, and an injection of the $n$ circuit qubits into the $N$ qubits, such that for the linear interpolation
--   $$K(t)=\Big(1-\frac t{T'}\Big)K_0+\frac t{T'}K_1,\qquad t\in[0,T'],$$
--   and its propagator $U$,
--   $$\tfrac12\Big\|\operatorname{Tr}_{\text{non-output}}\big(U_{T'}|0^N\rangle\langle0^N|U_{T'}^\dagger\big)-\mathcal C|0^n\rangle\langle0^n|\mathcal C^\dagger\Big\|_1\le\frac\varepsilon2.$$
--
--   This is the logical adiabatic path that the construction of Theorem 3.5 protects; it is a cited result of Aharonov et al. used in the proof.
--
--   Differences from the source:
--   - encoding: constant support, bounded operator norm, T′ = poly(n, T, ε^{−1}), N = O(n + T/ε) → explicit C with terms on ≤ C qubits of norm ≤ C, T′ ≤ C(2 + n + T + 1/ε)^C, N ≤ C(n + (T+1)/ε); reason: the O and poly constants are absolute; T + 1 and 2 + keep the bounds meaningful at T = 0
--   - reading: the logical Hamiltonian path K(t) = Σ_q K_q(t) of [AVDK+08] → the linear interpolation (1 − t/T′)K_0 + (t/T′)K_1 of sums of local Hermitian terms, started in |0…0⟩, a ground state of K_0; reason: this is the form the paper records on p. 9 (third bullet); AVDK's initial ground state is the all-zero input with the clock at 0
--   - reading: approximation error at most ε/2 → trace distance ½‖·‖₁ ≤ ε/2 between the reduced state of the output qubits at T′ and the circuit output; reason: the simulation notion of p. 11
--   - reading: every term K_q has constant support and bounded operator norm → in addition, for every qubit set S the sum of the terms of K_0 (resp. K_1) whose support is exactly S has norm ≤ C; reason: bounded interaction strength is a bound on the interaction on each set of qubits; without it one term repeated λ times counts as λ terms of norm ≤ C and the path can be sped up arbitrarily; the AVDK terms on a given support are O(1) many
-- source:
--   Arsalan Motamedi, Peter Love, Fault Tolerant Adiabatic Quantum Computation from Passive Error Correcting Codes, STOC 2027 submission #1144 (October 2026), source.pdf SHA-256 96d4a748a9114e6a9ed0c5252e84434a63b2a1ef07b286134f01f6761c2503b8, p. 25, proof of Theorem 3.5, (3.41)–(3.42); the interpolation form from p. 9, third bullet

import Mathlib
import Definitions.Def_PassiveAdiabaticFT_Thermal_Operators

set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix

namespace PassiveAdiabaticFT.Thermal

/-- Proof of Theorem 3.5, (3.41)–(3.42) (p. 25): the circuit-to-adiabatic reduction of
[AVDK+08] with error `ε/2`. Every circuit of `T` gates on `n` qubits is simulated by a linear
interpolation `K(t) = (1 − t/T')K_0 + (t/T')K_1` on `N = O(n + T/ε)` qubits, started in
`|0…0⟩` (a ground state of `K_0`), with `O(1)`-local terms of `O(1)` norm (also after merging
the terms of `K_0`, resp. `K_1`, that have the same support) and
`T' = poly(n, T, 1/ε)`: the reduced state of the output qubits at time `T'` is within trace
distance `ε/2` of `𝒞|0ⁿ⟩`. -/
theorem avdk_reduction :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (T : ℕ) (ε : ℝ), 0 < ε → ∀ circ : Circuit n T,
      ∃ (N : ℕ) (T' : ℝ) (r0 r1 : ℕ) (K0 : Fin r0 → Op (Fin N)) (K1 : Fin r1 → Op (Fin N))
        (out : Fin n ↪ Fin N),
        (N : ℝ) ≤ C * (n + ((T : ℝ) + 1) / ε) ∧ 0 < T' ∧
        T' ≤ C * (2 + n + T + 1 / ε) ^ C ∧
        (∀ A, (K0 A)ᴴ = K0 A ∧ OpNormLe (K0 A) C ∧
          ∃ S : Finset (Fin N), (S.card : ℝ) ≤ C ∧ ActsOn (K0 A) S) ∧
        (∀ A, (K1 A)ᴴ = K1 A ∧ OpNormLe (K1 A) C ∧
          ∃ S : Finset (Fin N), (S.card : ℝ) ≤ C ∧ ActsOn (K1 A) S) ∧
        (∀ S : Finset (Fin N), OpNormLe (termsOn K0 S) C ∧ OpNormLe (termsOn K1 S) C) ∧
        IsGroundState (∑ A, K0 A) ketZero ∧
        ∀ U : ℝ → Op (Fin N),
          IsPropagator
              (fun t => (((1 - t / T' : ℝ)) : ℂ) • ∑ A, K0 A + (((t / T' : ℝ)) : ℂ) • ∑ A, K1 A)
              T' U →
            traceDist (reduceTo out (U T' * ketbraZero * (U T')ᴴ)) circ.output ≤ ε / 2 := by sorry

end PassiveAdiabaticFT.Thermal
