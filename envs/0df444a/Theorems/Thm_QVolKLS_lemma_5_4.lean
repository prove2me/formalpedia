-- Prove2me | Theorems.Thm_QVolKLS_lemma_5_4
-- name    : QVolKLS.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:38:42.142884+00:00
-- url     : https://prove2.me/theorems/59ff4837-f25e-4e2b-9e79-f76055758fe8
-- title:
--   Lemma 5.4 — qsample conversion with $O(f_0^{-1/2}\log(1/\varepsilon))$ controlled reflections
-- statement:
--   There is an absolute constant $C>0$ such that the following holds for every finite sample space $\Omega=\{0,1\}^s$, every known $0<f_0\le1$ and every $0<\varepsilon<\tfrac12$. There is one circuit, making at most
--   $$
--   C\,f_0^{-1/2}\log(1/\varepsilon)
--   $$
--   calls to controlled qsample reflections, such that for all probability distributions $\pi,\nu$ on $\Omega$ with $|\langle\pi|\nu\rangle|^2\ge f_0$, given exact controlled access to $R_\pi=2|\pi\rangle\langle\pi|-I$ and $R_\nu=2|\nu\rangle\langle\nu|-I$, it maps a supplied qsample $|\pi\rangle_S$ (with workspace in $|0\rangle$) to $|0\rangle\otimes|\tilde\nu\rangle_S$ with
--   $$
--   d_{\mathrm{tr}}\big(|\tilde\nu\rangle\langle\tilde\nu|,\,|\nu\rangle\langle\nu|\big)\le\varepsilon .
--   $$
--
--   This converts a qsample of one cooling stage into the next.
--
--   **Formalization Note** Arbitrary unitary gates; oracle $0$ is $R_\pi$, oracle $1$ is $R_\nu$; plain, inverse and controlled calls each count one. The circuit is fixed from $s,f_0,\varepsilon$ before $\pi,\nu$.
--
--   Differences from the source:
--   - encoding: π, ν on a common finite set Ω → laws on {0,1}^s; reason: every finite set embeds in {0,1}^s with zero weight on unused labels
--   - reading: there is a circuit … using O(f₀^{-1/2} log(1/ε)) controlled qsample reflections → one circuit over arbitrary unitary gates, chosen from s, f₀, ε before π and ν, with ≤ C f₀^{-1/2} log(1/ε) calls; reason: the reflections are the only access to π and ν; a circuit chosen after them could prepare |ν⟩ with no call
--   - reading: maps a supplied qsample |π⟩_S to a state |ν̃⟩_S → |0^a⟩|π⟩ ↦ |0^a⟩|ν̃⟩ exactly, workspace returned to |0⟩; reason: the output is a pure state of S; the construction returns its control qubit to zero (p.43)
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), Lemma 5.4, p.42

import Definitions.Def_QVolKLS_fourthMomentNorm

set_option autoImplicit false

namespace QVolKLS

open QAlgorithms

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **Lemma 5.4 (Qsample conversion
[YLC14])**, p.42.

There is an absolute `C > 0` such that for every sample register of `s` qubits (sample space
`Ω = {0,1}^s`), every known `0 < f₀ ≤ 1` and every `0 < ε < 1/2` there is one circuit, using at most
`C f₀^{−1/2} log(1/ε)` calls to the controlled qsample reflections `R_π`, `R_ν`, such that for all
probability laws `π`, `ν` on `Ω` with `|⟨π|ν⟩|² ≥ f₀` it maps the supplied qsample `|0^a⟩ ⊗ |π⟩_S`
to `|0^a⟩ ⊗ |ν̃⟩_S` with `d_tr(|ν̃⟩⟨ν̃|, |ν⟩⟨ν|) ≤ ε`.

**Formalization Note.** The circuit uses arbitrary unitary gates (`unitaryGateSet`; the lemma counts
reflections only) and two oracles of arity `s`: oracle `0` is `R_π`, oracle `1` is `R_ν`; plain,
inverse and controlled calls each count one. It is chosen from `s`, `f₀`, `ε` before `π` and `ν`,
which it sees only through the oracles. Workspace (`a` qubits, first wires) starts and ends in
`|0⟩`. A law on any finite set is placed on `Ω` with zero weight on unused labels. -/
theorem lemma_5_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℕ) (f0 ε : ℝ), 0 < f0 → f0 ≤ 1 → 0 < ε → ε < 1 / 2 →
      ∃ (a : ℕ) (c : OracleCircuit unitaryGateSet (fun _ : Fin 2 => s) (a + s)),
        ((c.queryCount 0 + c.queryCount 1 : ℕ) : ℝ) ≤ C * f0 ^ (-(1 / 2 : ℝ)) * Real.log (1 / ε) ∧
        ∀ π ν : Qubits s → ℝ, (∀ x, 0 ≤ π x) → ∑ x, π x = 1 → (∀ x, 0 ≤ ν x) → ∑ x, ν x = 1 →
          f0 ≤ ‖∑ x, qsample π x * qsample ν x‖ ^ 2 →
          ∃ νt : Qubits s → ℂ,
            opApply (c.unitary (fun k => if k = 0 then qsampleRefl π else qsampleRefl ν))
                (withZeroAnc a (qsample π)) = withZeroAnc a νt ∧
            traceDist (pureDensity νt) (pureDensity (qsample ν)) ≤ ε := by sorry

end QVolKLS
