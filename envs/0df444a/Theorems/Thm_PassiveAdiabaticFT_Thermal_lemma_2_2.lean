-- Prove2me | Theorems.Thm_PassiveAdiabaticFT_Thermal_lemma_2_2
-- name    : PassiveAdiabaticFT.Thermal.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:31.478195+00:00
-- url     : https://prove2.me/theorems/0af3409e-a3ca-4578-aa7b-f70200f220ae
-- title:
--   Lemma 2.2 — Pauli errors in the $W$ representation
-- statement:
--   Let $C$ be a stabilizer code with encoder $V$, let $\{R_s\}_{s\in\Omega}$ be a Pauli decoder and $W$ the unitary of (1.4). For a single-qubit Pauli $F_\alpha$ let $e_\alpha\in\{0,1\}^A$ be defined by $P_aF_\alpha=(-1)^{(e_\alpha)_a}F_\alpha P_a$ (2.2), $f_\alpha(s)=s\oplus e_\alpha$, and $G_s^{(\alpha)}=V^\dagger R_{f_\alpha(s)}F_\alpha R_s^\dagger V$ (2.3). Then $f_\alpha$ maps $\Omega$ into $\Omega$ and permutes it,
--   $$W^\dagger F_\alpha W=\sum_{s\in\Omega}G_s^{(\alpha)}\otimes|f_\alpha(s)\rangle\langle s|,$$
--   and $G_{f_\alpha(s)}^{(\alpha)}=(G_s^{(\alpha)})^\dagger$ for every $s\in\Omega$.
--
--   The block form says that a single-qubit Pauli moves the syndrome deterministically and acts on the logical register by $G_s^{(\alpha)}$; it underlies the definition of dangerous syndromes and every later bound.
--
--   Differences from the source:
--   - encoding: operators on (ℂ²)^{⊗b}, syndromes s ∈ {0,1}^A, the syndrome register spanned by |s⟩, s ∈ Ω → complex matrices indexed by bit strings Fin b → Fin 2, syndromes Fin m → ZMod 2, the register indexed by the subtype Ω; reason: the same vectors and operators in coordinates
--   - encoding: f_α : Ω → Ω is a syndrome permutation with f_α(•) = • ⊕ e_α for some e_α ∈ {0,1}^A (item 1) → f_α(s) := s + e_α with e_α the syndrome of F_α from (2.2); the Lean states that f_α maps Ω into Ω, that the induced map on Ω is bijective, and (as a definitional clause) item 1; reason: the proof's (2.2) is the definition of e_α; the permutation claim is kept as explicit clauses
-- source:
--   Arsalan Motamedi, Peter Love, Fault Tolerant Adiabatic Quantum Computation from Passive Error Correcting Codes, STOC 2027 submission #1144 (October 2026), source.pdf SHA-256 96d4a748a9114e6a9ed0c5252e84434a63b2a1ef07b286134f01f6761c2503b8, pp. 12–13, Lemma 2.2, eqs. (2.1)–(2.4)

import Mathlib
import Definitions.Def_PassiveAdiabaticFT_Thermal_CodeBlock

set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix

namespace PassiveAdiabaticFT.Thermal

/-- Lemma 2.2 (pp. 12–13): `W† F_α W = Σ_{s ∈ Ω} G_s^{(α)} ⊗ |f_α(s)⟩⟨s|`, where `f_α` is a
syndrome permutation of `Ω` with `f_α(s) = s ⊕ e_α`, and `G_{f_α(s)}^{(α)} = (G_s^{(α)})†`. -/
theorem lemma_2_2 {b : ℕ} (C : StabCode b) (D : PauliDecoder C) (α : Fin b × Fin 3) :
    (∀ s ∈ C.Omega, C.f α s ∈ C.Omega) ∧
    Function.Bijective (C.fOm α) ∧
    D.Wᴴ * Fα α * D.W =
      (fun p q => if p.2 = C.fOm α q.2 then D.G α q.2.1 p.1 q.1 else 0) ∧
    (∀ s, C.f α s = s + C.e α) ∧
    (∀ s ∈ C.Omega, D.G α (C.f α s) = (D.G α s)ᴴ) := by sorry

end PassiveAdiabaticFT.Thermal
