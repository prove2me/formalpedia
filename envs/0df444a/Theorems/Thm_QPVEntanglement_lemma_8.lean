-- Prove2me | Theorems.Thm_QPVEntanglement_lemma_8
-- name    : QPVEntanglement.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:34:38.477842+00:00
-- url     : https://prove2.me/theorems/d337ff38-258f-48ce-986c-f20770c2bf16
-- title:
--   Lemma 8 — the verifier's action raises $E_{sq}$ by at most $R_H$
-- statement:
--   This mission states the paper's results in the **operator-requested pinned-down model** of its §4 adversary model; this item is a pure quantum-information statement and does not depend on that model.
--
--   Suppose $O$ contains at most $R_H$ verifier reference qubits and $OA_0A_1$ is pure after the earlier classical records are fixed. Let $\rho_-$ be the adversarial state immediately before the verifier acts, with any response waiting or travelling to the verifier still on its sender's side, and $\rho_+$ the state after the verifier acts at the deadline of the challenge slot. Then
--
--   $$E_{sq}(A_0:A_1)_{\rho_+}\le E_{sq}(A_0:A_1)_{\rho_-}+R_H,$$
--
--   irrespective of whether a response is sent from either side or no response is sent (footnote 27). It bounds the only non-LOCC step of a round in the security proof.
--
--   Differences from the source:
--   - encoding: E_sq = ½ inf over all extensions ω_ABE of I(A:B|E) → published `squashed`: ½·sInf of the conditional mutual information (bits) over density-matrix extensions with environment `Fin e`, every e > 0; reason: every finite-dimensional extension is isomorphic to one with E = Fin e; same quantity
--   - reading: O contains at most R_H reference qubits, OA0A1 pure after the earlier records are fixed, ρ− before and ρ+ after the verifier acts → O = Fin r → Fin 2 with r ≤ R_H; record c (probability p_c, held on side A0) with pure ψ_c on O × A0 × A1; the response register W a tensor factor of the sender's side (two conjuncts, W on A0 or on A1; W may be one-dimensional); ρ− = Σ_c p_c|c⟩⟨c| ⊗ Tr_O|ψ_c⟩⟨ψ_c|, ρ+ = `afterVerifier`; reason: the state description of the lemma and of its proof (p.74); by Lemma 1 the placement of the record is immaterial
--   - generalization: the respective verifier acts at the deadline (BB84 projection test, or discarding the reference when no response arrives) → an arbitrary POVM {E_z} on O ⊗ W whose outcome is kept as a classical record, after which O and W are removed; reason: the proof, (103)–(104), uses only that the verifier acts on O and W; the projection test and the discard are such measurements
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Lemma 8, p.44, and footnote 27; proof App. C.2, p.74

import Mathlib
import Definitions.Def_QPVEntanglement_afterVerifier

set_option autoImplicit false

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P19 (squashed)

namespace QPVEntanglement

/-- **Lemma 8 (the verifier's action raises `E_sq` by at most `R_H`)**, p.44 (proof App. C.2,
p.74). Behera–Goyal, arXiv:2609.39234 (sha256 bdf2928d…), Lemma 8, p.44, and footnote 27.

Suppose `O` contains at most `R_H` verifier reference qubits and `OA₀A₁` is pure after the earlier
classical records are fixed. Let `ρ₋` be the adversarial state immediately before the verifier
acts, with any response still on its sender's side, and `ρ₊` the state after the verifier acts
at the deadline. Then `E_sq(A₀ : A₁)_{ρ₊} ≤ E_sq(A₀ : A₁)_{ρ₋} + R_H`, whichever side sends the
response and also when none is sent (footnote 27).

**Formalization Note.** Pinned QIT form: `O` is `r ≤ R_H` qubits; the earlier record `c` (on
side `A₀`; by Lemma 1 the placement is immaterial) has probability `p c` and pure conditional
state `ψ_c` on `O × A₀ × A₁`; the response register `W` is a tensor factor of the sender's side
(first conjunct: `A₀ = W × A₀'`; second: `A₁ = W × A₁'`; `W` may be one-dimensional, "no
response"). The verifier's action is an arbitrary measurement (POVM `{E_z}`) on `O × W` whose
outcome `z` is kept as a classical record, after which `O` and `W` are removed; this generalizes
the BB84 projection test (the proof, (103)–(104), uses only that the action is on `O` and `W`).
`ρ₋ = Σ_c p_c |c⟩⟨c| ⊗ Tr_O |ψ_c⟩⟨ψ_c|`, `ρ₊ = afterVerifier …`. -/
theorem lemma_8 (RH r : ℕ) (hr : r ≤ RH) {C Z W A0 A1 : Type*} [Fintype C] [DecidableEq C]
    [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W] [Fintype A0] [DecidableEq A0]
    [Fintype A1] [DecidableEq A1] (p : C → ℝ) (hp : IsProbVec p)
    (E : Z → Matrix ((Fin r → Fin 2) × W) ((Fin r → Fin 2) × W) ℂ)
    (hE : (∀ z, (E z).PosSemidef) ∧ ∑ z, E z = 1) :
    (∀ ψ : C → (Fin r → Fin 2) × ((W × A0) × A1) → ℂ, (∀ c, IsUnitVec (ψ c)) →
      squashed (afterVerifier p ψ E) ≤
        squashed (recordOnLeft p fun c => QAlgorithms.traceLeft (pureDensity (ψ c))) + RH) ∧
    (∀ ψ : C → (Fin r → Fin 2) × (A0 × (W × A1)) → ℂ, (∀ c, IsUnitVec (ψ c)) →
      squashed (afterVerifierRight p ψ E) ≤
        squashed (recordOnLeft p fun c => QAlgorithms.traceLeft (pureDensity (ψ c))) + RH) := by sorry

end QPVEntanglement
