-- Prove2me | Theorems.Thm_QuantumGroupCodes836_Addressability_modulation_circuit
-- name    : QuantumGroupCodes836.Addressability.modulation_circuit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T17:14:30.028433+00:00
-- url     : https://prove2.me/theorems/cf8b3aab-4ab7-4f63-ab45-7e792d1e5b5f
-- title:
--   Lemma 3.10 — modulation realizes circuits (corrected: dual-distance hypothesis)
-- statement:
--   Use the corrected construction, its canonical encoding, and any equivariant section $s$ of the quotient map (one exists). For any logical subset $S$, weights $\lambda$, shared group shifts $\sigma_1,\ldots,\sigma_{m-1}$ and encoded state $|\psi\rangle$, let $\Lambda=sE(1_S\star\lambda\star u_L^{-1})$. Then
--
--   $$\prod_{Q\in S}C^{m-1}Z_{\lambda_Q}[Q,\sigma_1Q,\ldots,\sigma_{m-1}Q]|\psi\rangle=
--   \prod_{P\in J}C^{m-1}Z_{u_P\Lambda_P}[P,\sigma_1P,\ldots,\sigma_{m-1}P]|\psi\rangle.$$
--
--   The statement is equality on every encoded complex state. Modulation is computed from the section and encoding, and the physical product runs over actual remaining coordinates.
--
--   Differences from the source:
--   - encoding: CSS codes and module-linear sections → actual normalized coset subspaces and equivariant linear sections of actual quotients; reason: these are equivalent finite-coordinate models, with computed logical dimension and quotient-weight distance
--   - correction: d(C^perp)>|G| → d(C^perp)>r|G|; reason: C2: three independent length-four repetition blocks with trivial G and two selected singleton orbits satisfy the printed assumptions but give logical dimension 1 instead of 2
--   - encoding: products of diagonal trace phases → the exponential of the summed field phase, on all amplitudes; reason: additivity of field trace and the exponential makes these exactly the same operators
--   - generalization: Λ = s∘E(1_S⋆λ⋆u_L^{-1}) with the section s of (7) → the identity for every module-linear section s whose action is the shift on the remaining coordinates (and such a section exists); reason: the section (7) is one of these, so the Lean statement specializes to the source; the proof only uses π∘s = id
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Lemma 3.10, pp.12–13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Definitions.Def_QuantumGroupCodes836_Addressability_Construction

set_option autoImplicit false
open scoped Classical

namespace QuantumGroupCodes836.Addressability

theorem modulation_circuit {F G : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] [Group G] [Fintype G]
    {n r m : ℕ} (C : Code F (Fin n)) (A : CodeAction F (Fin n) G C)
    (p : Fin r → Fin n) (u : Fin n → F) (h : ConstructionAssumptions C A p m u) : ModulationIdentity C A p m u := by sorry

end QuantumGroupCodes836.Addressability
