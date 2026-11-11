-- Prove2me | Theorems.Thm_QuadSDE_lemma_8
-- name    : QuadSDE.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:15:44.143407+00:00
-- url     : https://prove2.me/theorems/c597ea3d-20e5-4e84-88b9-8f245bba836a
-- title:
--   Lemma 8 (LCHS simulation) — $\|\nu(\langle0^b|\otimes I)U(|0^b\rangle\otimes I)-\mathcal T\exp(-\int_0^T(L+iH))\|\le\eta$ with $\tilde O(1+T\alpha)$ queries
-- statement:
--   There are universal constants $\nu_0>0$, $C$ and $c$ such that the following holds. Let $n$ be the number of data qubits, $b_L,b_H$ the ancilla counts of the block encodings, $T\ge0$, $\alpha$, known normalizations $0<\alpha_L,\alpha_H\le\alpha$, a derivative bound $\beta\ge0$, and $0<\eta<1/2$; write $\Lambda=\log(2+T+T\alpha+T\beta+1/\eta)$. Then there are a time-register size $m_T\le C\Lambda^c$, an ancilla count $b\le b_L+b_H+m_T+C\Lambda^c$, a normalization $0<\nu\le\nu_0$ and one quantum circuit $U$ over $\{H,T,\mathrm{CNOT}\}$ on $b+n$ qubits, making at most $C(1+T\alpha)\Lambda^c$ calls to the two time-controlled oracles $O_L=\sum_\tau|\tau\rangle\langle\tau|\otimes U_L(\tau T/2^{m_T})$ and $O_H=\sum_\tau|\tau\rangle\langle\tau|\otimes U_H(\tau T/2^{m_T})$ (controlled and inverse calls included) and using at most $C(1+T\alpha)(\Lambda+b_L+b_H)^c$ gates, such that: for all continuously differentiable families $L(t)\succeq0$ and $H(t)=H(t)^\dagger$ on $[0,T]$ with $\|L'(t)\|,\|H'(t)\|\le\beta$, and all exact block encodings $U_L(t)$ of $L(t)/\alpha_L$ and $U_H(t)$ of $H(t)/\alpha_H$,
--   $$\Big\|\nu(\langle0^b|\otimes I)U(|0^b\rangle\otimes I)-\mathcal T\exp\Big(-\int_0^T(L(t)+iH(t))\,dt\Big)\Big\|\le\eta\qquad(63).$$
--
--   This is the linear-combination-of-Hamiltonian-simulations primitive of Low and Somma [LS25], which the algorithm applies to the projected Kolmogorian $K_k(t)=-A_k(t)-iH_k(t)$.
--
--   Differences from the source:
--   - reading: access to controlled block encodings of L(t) and H(t) with normalization at most α → two oracles O_L = Σ_τ |τ⟩⟨τ| ⊗ U_L(τT/2^{m_T}), O_H likewise, on a time register of m_T qubits chosen with the circuit; U_L(t), U_H(t) exact block encodings (ancillas first) of L(t), H(t) with known normalizations 0 < α_L, α_H ≤ α; controlled and inverse calls allowed; reason: this is the form of Eq. (81), p. 30, in which the lemma is applied
--   - reading: known bounds on their time derivatives; L(t), H(t) continuously differentiable → a given β ≥ 0 with spectral norms ‖L′(t)‖, ‖H′(t)‖ ≤ β on [0, T]; entrywise derivatives within [0, T], continuous on [0, T]; reason: the derivative bound is an input of the construction
--   - reading: a known normalization ν = O(1) bounded by a universal constant independent of T, α, and η → ∃ ν₀ > 0 before all parameters; the circuit's ν ∈ (0, ν₀] is chosen with the circuit, before the oracles; reason: a universal constant precedes everything
--   - reading: Õ(1 + Tα) queries, the tilde suppressing polylogarithmic factors in the accuracy and simulation parameters → queryCount(O_L) + queryCount(O_H) ≤ C (1 + Tα) log(2 + T + Tα + Tβ + 1/η)^c with universal C, c; reason: polylog factors in the accuracy 1/η and the simulation parameters T, Tα, Tβ; T must appear, since the oracles reveal L only on the grid τT/2^{m_T}: with Tα = Tβ = 1 and T → ∞, a bump of L between grid points changes 𝒯exp by a constant unless 2^{m_T} ≳ T/η
--   - reading: additional gate and space costs are polynomial in the precision and the cost of implementing the controlled encodings → gateCount ≤ C (1 + Tα)(Λ + b_L + b_H)^c, m_T ≤ C Λ^c, b ≤ b_L + b_H + m_T + C Λ^c with Λ = log(2 + T + Tα + Tβ + 1/η); reason: precision is read as log(1/η), the stronger reading; the encodings' cost enters through their ancilla counts
--   - reading: there is a quantum circuit U … 𝒯exp(−∫₀ᵀ (L + iH) dt) → one OracleCircuit over {H, T, CNOT}, fixed before the oracles and correct for all of them; 𝒯exp is V(T) for every solution of V′ = −(L + iH)V, V(0) = I on [0, T]; reason: the circuit cannot depend on the black boxes; the matrix ODE has a unique solution
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §4.6, Lemma 8, p. 27 (cited from Low and Somma [LS25])

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_CircuitResources
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QuadSDE_LCHS

open QAlgorithms
open scoped ComplexOrder

namespace QuadSDE

/-- **Lemma 8 (LCHS simulation).**
Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), §4.6, Lemma 8, p. 27 (cited
from Low and Somma [LS25]): "Let `L(t) ⪰ 0` and `H(t) = H(t)†` be continuously differentiable, and
assume we are given access to controlled block encodings of `L(t)` and `H(t)` with normalization at
most `α` and with known bounds on their time derivatives. For any `0 < η < 1/2`, there is a quantum
circuit `U` acting on the data register and `b` ancilla qubits such that
`‖ν(⟨0^b| ⊗ I)U(|0^b⟩ ⊗ I) − 𝒯exp(−∫_0^T (L(t) + iH(t)) dt)‖ ≤ η` (63) for a known normalization
`ν = O(1)` bounded by a universal constant independent of `T`, `α`, and `η`. The circuit uses
`Õ(1 + Tα)` queries to the block-encodings, where the tilde suppresses polylogarithmic factors in
the accuracy and simulation parameters. Its additional gate and space costs are polynomial in the
precision and the cost of implementing the controlled encodings."

There are universal constants `ν₀ > 0`, `C` and `c` such that for all sizes `n` (data qubits),
`b_L, b_H` (encoding ancillas), every `T ≥ 0`, `α`, known normalizations `0 < α_L, α_H ≤ α`, every
derivative bound `β ≥ 0` and every `0 < η < 1/2`, there are a time-register size `m_T`, an ancilla
count `b`, a normalization `0 < ν ≤ ν₀` and one oracle circuit `U` over `{H, T, CNOT}` on `b + n`
qubits, calling `O_L` and `O_H`, with (writing `Λ = log(2 + T + Tα + Tβ + 1/η)`)
`m_T ≤ C Λ^c`, `b ≤ b_L + b_H + m_T + C Λ^c`, at most `C (1 + Tα) Λ^c` oracle queries and at most
`C (1 + Tα)(Λ + b_L + b_H)^c` gates, such that: for all `C¹` families `L(t) ⪰ 0`, `H(t) = H(t)†`
on `[0, T]` with `‖L′(t)‖, ‖H′(t)‖ ≤ β`, all exact block encodings `U_L(t)` of `L(t)` with
normalization `α_L` and `U_H(t)` of `H(t)` with normalization `α_H` (`t ∈ [0, T]`), with
`O_L = Σ_τ |τ⟩⟨τ| ⊗ U_L(τT/2^{m_T})` and `O_H` likewise, and for the propagator
`V(T) = 𝒯exp(−∫_0^T (L + iH))`, the ancilla-zero block of `U` satisfies
`‖ν (⟨0^b| ⊗ I) U (|0^b⟩ ⊗ I) − V(T)‖ ≤ η` (operator norm).

**Formalization Note.** Readings of the cited, informally stated lemma: (a) "access to controlled
block encodings of `L(t)` and `H(t)`" is access to the time-controlled oracles of Eq. (81)
(`lchsOracles`, time grid chosen by the circuit), with controlled and inverse calls; (b) "known
bounds on their time derivatives" is a given `β` with `‖L′‖, ‖H′‖ ≤ β` (spectral norm);
(c) "`ν = O(1)` bounded by a universal constant" is `ν ≤ ν₀` with `ν₀` chosen before everything;
(d) `Õ(1 + Tα)` queries is `C (1 + Tα) Λ^c`, the polylogarithm taken in the simulation parameters
`T, Tα, Tβ` and the accuracy `1/η` (`T` must appear: the oracles reveal `L, H` only on the grid
`τT/2^{m_T}`, and with `Tα = Tβ = 1`, `T → ∞` a bump of `L` between grid points changes `V(T)` by a
constant unless `2^{m_T} ≳ T/η`); (e) "polynomial in the precision and the cost of the
encodings" is read with precision `log(1/η)` (the stronger reading) and encoding cost `b_L + b_H`.
The circuit is chosen before the oracles and works for all of them. Block encodings are exact
(`ε = 0`), ancillas first (`IsQubitBlockEncoding`). `C¹` is entrywise with continuous derivative
on `[0, T]`. -/
theorem lemma_8 :
    ∃ (ν₀ C : ℝ) (c : ℕ), 0 < ν₀ ∧
      ∀ (n bL bH : ℕ) (T α αL αH β η : ℝ), 0 ≤ T → 0 < αL → αL ≤ α → 0 < αH → αH ≤ α →
        0 ≤ β → 0 < η → η < 1 / 2 →
        ∃ (mT b : ℕ) (ν : ℝ) (U : OracleCircuit htcxGateSet (lchsArity mT bL bH n) (b + n)),
          0 < ν ∧ ν ≤ ν₀ ∧
          (mT : ℝ) ≤ C * Real.log (2 + T + T * α + T * β + 1 / η) ^ c ∧
          (b : ℝ) ≤ bL + bH + mT + C * Real.log (2 + T + T * α + T * β + 1 / η) ^ c ∧
          ((U.queryCount 0 + U.queryCount 1 : ℕ) : ℝ) ≤
            C * (1 + T * α) * Real.log (2 + T + T * α + T * β + 1 / η) ^ c ∧
          (U.gateCount : ℝ) ≤
            C * (1 + T * α) * (Real.log (2 + T + T * α + T * β + 1 / η) + bL + bH) ^ c ∧
          ∀ (L H L' H' : ℝ → Matrix (Qubits n) (Qubits n) ℂ)
            (UL : ℝ → Matrix (Qubits (bL + n)) (Qubits (bL + n)) ℂ)
            (UH : ℝ → Matrix (Qubits (bH + n)) (Qubits (bH + n)) ℂ)
            (V : ℝ → Matrix (Qubits n) (Qubits n) ℂ),
            (∀ t ∈ Set.Icc (0 : ℝ) T, (L t).PosSemidef ∧ (H t).IsHermitian) →
            (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i j,
              HasDerivWithinAt (fun s => L s i j) (L' t i j) (Set.Icc 0 T) t ∧
              HasDerivWithinAt (fun s => H s i j) (H' t i j) (Set.Icc 0 T) t) →
            (∀ i j, ContinuousOn (fun t => L' t i j) (Set.Icc 0 T) ∧
              ContinuousOn (fun t => H' t i j) (Set.Icc 0 T)) →
            (∀ t ∈ Set.Icc (0 : ℝ) T, specNorm (L' t) ≤ β ∧ specNorm (H' t) ≤ β) →
            (∀ t ∈ Set.Icc (0 : ℝ) T,
              IsQubitBlockEncoding bL n (UL t) αL 0 (L t) ∧
              IsQubitBlockEncoding bH n (UH t) αH 0 (H t)) →
            IsPropagator (fun t => -(L t + Complex.I • H t)) T V →
            specNorm ((ν : ℂ) • blockOf (U.unitary (lchsOracles mT bL bH n T UL UH)) - V T) ≤ η := by sorry

end QuadSDE
