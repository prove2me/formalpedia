-- Prove2me | Theorems.Thm_PassiveAdiabaticFT_Thermal_lemma_2_7
-- name    : PassiveAdiabaticFT.Thermal.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:37.406196+00:00
-- url     : https://prove2.me/theorems/f8e27ca6-feaa-423d-af3e-9ad6bd85f909
-- title:
--   Lemma 2.7 — low-energy decoder
-- statement:
--   Let $C$ be a stabilizer code on $b$ qubits with encoder $V$ and $k$ logical qubits, $J$ the penalty, $\Delta_b$ its logical energy barrier (1.27) and $\delta_b$ the maximal single-Pauli energy change (2.16). For every $\tilde\Delta$ with $0<\tilde\Delta<\Delta_b/2$ there is a Pauli decoder $\{R_s\}_{s\in\Omega}$ with $R_0=I$ such that
--   $$\bigcup_\alpha D_\alpha\subseteq\Omega_{>\tilde\Delta-\delta_b}\qquad(2.17)$$
--   and, for all $\beta,\beta'\ge0$,
--   $$\frac{Z(\beta)}{Z(\beta')}\,\pi_\beta\Big(\bigcup_\alpha D_\alpha\Big)\le2^{b-k}\exp\big[-\beta(\tilde\Delta-\delta_b)\big].\qquad(2.18)$$
--
--   This is the source of exponentially rare dangerous syndromes: a macroscopic barrier lets a decoder protect every low-energy syndrome against every single-qubit Pauli.
--
--   Differences from the source:
--   - encoding: operators on (ℂ²)^{⊗b}, syndromes s ∈ {0,1}^A, the syndrome register spanned by |s⟩, s ∈ Ω → complex matrices indexed by bit strings Fin b → Fin 2, syndromes Fin m → ZMod 2, the register indexed by the subtype Ω; reason: the same vectors and operators in coordinates
--   - encoding: block length n and 2^{n−k} → block length b and (2:ℝ)^(b − k) with natural subtraction; reason: k ≤ b because V is an isometry, so no truncation occurs
--   - encoding: Δ_n, δ_n as energies → 2J times the barrier and the maximal change in violated checks; reason: E[s] = 2J|s| (1.7)
-- source:
--   Arsalan Motamedi, Peter Love, Fault Tolerant Adiabatic Quantum Computation from Passive Error Correcting Codes, STOC 2027 submission #1144 (October 2026), source.pdf SHA-256 96d4a748a9114e6a9ed0c5252e84434a63b2a1ef07b286134f01f6761c2503b8, p. 15, Lemma 2.7 (2.17)–(2.18) (proof pp. 15–16)

import Mathlib
import Definitions.Def_PassiveAdiabaticFT_Thermal_CodeBlock

set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix

namespace PassiveAdiabaticFT.Thermal

/-- Lemma 2.7 (low-energy decoder, p. 15): for every `Δ̃` with `0 < Δ̃ < Δ_b/2` there is a Pauli
decoder with `R_0 = I` such that `⋃_α D_α ⊆ Ω_{>Δ̃ − δ_b}` (2.17), and for all `β, β' ≥ 0`,
`(Z(β)/Z(β')) π_β(⋃_α D_α) ≤ 2^{b−k} exp[−β(Δ̃ − δ_b)]` (2.18). -/
theorem lemma_2_7 {b : ℕ} (C : StabCode b) (J Δt : ℝ) (h0 : 0 < Δt)
    (h1 : Δt < C.barrier J / 2) :
    ∃ D : PauliDecoder C, D.Bdec ⊆ C.OmegaGt J (Δt - C.delta J) ∧
      ∀ β β' : ℝ, 0 ≤ β → 0 ≤ β' →
        C.Z J β / C.Z J β' * C.gibbsSet J β D.Bdec ≤
          (2 : ℝ) ^ (b - C.k) * Real.exp (-(β * (Δt - C.delta J))) := by sorry

end PassiveAdiabaticFT.Thermal
