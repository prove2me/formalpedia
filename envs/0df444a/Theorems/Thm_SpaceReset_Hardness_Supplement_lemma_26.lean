-- Prove2me | Theorems.Thm_SpaceReset_Hardness_Supplement_lemma_26
-- name    : SpaceReset.Hardness.Supplement.lemma_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:44:34.819767+00:00
-- url     : https://prove2.me/theorems/5a1c598a-0f45-44b6-adf3-5f1cc1a0112e
-- title:
--   Lemma 26 — entropy converse with two unrelated decoders
-- statement:
--   Let $\{\xi_x\}_{x\in[A]}$ be positive semidefinite operators on $E_0$ of total trace one, and let $V:E_0\to Y\otimes E_1\otimes G$ be an isometry independent of $x$. Write
--   $$\Omega_{XYE_1G}=\sum_x|x\rangle\langle x|\otimes V\xi_xV^\dagger .$$
--   A POVM $\{E_x\}$ on $E_0$ guesses $X$ with average error $e_0=1-\sum_x\operatorname{Tr}(E_x\xi_x)$. A POVM $\{F_z\}_{z\in[B]}$ on $E_1$ guesses $Z=f(X)$ with average error $e_1=1-\sum_x\operatorname{Tr}\big((I_Y\otimes F_{f(x)}\otimes I_G)V\xi_xV^\dagger\big)$; the two POVMs need not be related, and $f:[A]\to[B]$ is arbitrary. With $d_i=\dim E_i$,
--   $$\log d_0+\log d_1+S(G)_\Omega\ \ge\ S(XY)_\Omega+H(Z)_\Omega-F_A(e_0)-F_B(e_1),$$
--   where $F_D(e)=h_2(e)+e\log(D-1)$ for $D\ge2$ and $F_1(0)=0$. No uniformity or balance assumption is required.
--
--   Applied at zero error to every two-cut window, this lemma gives the converse $2q+\Gamma\ge\Pi(G)$ of Theorem 28.
--
--   Differences from the source:
--   - encoding: subnormalized ensemble of total trace one indexed by [A] → ξ : Fin A → PSD matrices on E0 with Σ_x Tr ξ_x = 1; reason: the same objects; A ≥ 1 and B ≥ 1 are forced
--   - encoding: F_D(e) = h₂(e) + e log(D − 1) for D ≥ 2 and F_1(0) = 0 → fanoTerm D e = h₂(e) + e·log₂(D − 1) for every D; reason: for D = 1 this is h₂(e), and a one-element POVM is the identity, so e = 0 and the value is F_1(0) = 0
--   - encoding: average errors and traces → real parts of the complex traces; reason: the traces are real for positive operators
--   - encoding: S(XY)_Ω, S(G)_Ω, H(Z)_Ω → von Neumann entropy in bits (platform ShadowTomography.QuantumLB.vnEntropy) of the block-diagonal XY marginal and of the G marginal, and Shannon entropy in bits of p_Z(z) = Σ_{f(x)=z} Tr ξ_x; reason: the marginals of Ω
--   - encoding: the displayed inequality → the same inequality written right-hand side ≤ left-hand side; reason: identical
-- source:
--   Rinka Miura, STOC 2027 submission #1715 (October 2026), The Complexity of Space–Reset Tradeoffs in Online Quantum Computation (held submission, no arXiv version; SHA-256 c2a340e2195da0d130bf10d936d56d4f1d4da805e644efb7fe1c36d9c904f3e5), Lemma 26, p. 39 (App. C.1)

import Mathlib
import Definitions.Def_SpaceReset_Hardness_Supplement_Entropy

set_option autoImplicit false

namespace SpaceReset.Hardness.Supplement

open Matrix SpaceReset.Hardness
open scoped ComplexOrder

/-- Lemma 26 (Entropy converse; standard entropy inequalities), App. C.1, p. 39.

`{ξ_x}_{x ∈ [A]}` is an ensemble of positive semidefinite operators on `E₀` of total trace one,
`V : E₀ → Y ⊗ E₁ ⊗ G` an isometry independent of `x`, and
`Ω_{XYE₁G} = Σ_x |x⟩⟨x| ⊗ V ξ_x V†`. A POVM `{E_x}` on `E₀` guesses `X` with average error
`e₀ = 1 − Σ_x Tr(E_x ξ_x)`; a POVM `{F_z}_{z ∈ [B]}` on `E₁` guesses `Z = f(X)` with average error
`e₁ = 1 − Σ_x Tr((I_Y ⊗ F_{f(x)} ⊗ I_G) V ξ_x V†)`. Then
`log d₀ + log d₁ + S(G) ≥ S(XY)_Ω + H(Z)_Ω − F_A(e₀) − F_B(e₁)` (base-two logarithms,
`dᵢ = dim Eᵢ`). -/
theorem lemma_26 {A B : ℕ} {E0 Y E1 Gs : Type} [Fintype E0] [DecidableEq E0] [Fintype Y]
    [DecidableEq Y] [Fintype E1] [DecidableEq E1] [Fintype Gs] [DecidableEq Gs]
    (ξ : Fin A → Matrix E0 E0 ℂ) (hξ : ∀ x, (ξ x).PosSemidef) (htr : ∑ x, (ξ x).trace = 1)
    (V : Matrix ((Y × E1) × Gs) E0 ℂ) (hV : Vᴴ * V = 1) (f : Fin A → Fin B)
    (Ein : Fin A → Matrix E0 E0 ℂ) (hEin : IsPOVM Ein)
    (Fout : Fin B → Matrix E1 E1 ℂ) (hFout : IsPOVM Fout) :
    let ω : Fin A → Matrix ((Y × E1) × Gs) ((Y × E1) × Gs) ℂ := fun x => V * ξ x * Vᴴ
    let liftF : Matrix E1 E1 ℂ → Matrix ((Y × E1) × Gs) ((Y × E1) × Gs) ℂ := fun F p p' =>
      if p.1.1 = p'.1.1 ∧ p.2 = p'.2 then F p.1.2 p'.1.2 else 0
    let e0 : ℝ := 1 - (∑ x, (Ein x * ξ x).trace).re
    let e1 : ℝ := 1 - (∑ x, (liftF (Fout (f x)) * ω x).trace).re
    let ΩG : Matrix Gs Gs ℂ := ∑ x, ptraceLeft (ω x)
    let ΩXY : Matrix (Fin A × Y) (Fin A × Y) ℂ := fun p p' =>
      if p.1 = p'.1 then ptraceRight (ptraceRight (ω p.1)) p.2 p'.2 else 0
    let pZ : Fin B → ℝ := fun z => ∑ x ∈ Finset.univ.filter (fun x => f x = z), (ξ x).trace.re
    ShadowTomography.QuantumLB.vnEntropy ΩXY + shannonEntropy pZ - fanoTerm A e0 - fanoTerm B e1 ≤
      Real.logb 2 (Fintype.card E0) + Real.logb 2 (Fintype.card E1) + ShadowTomography.QuantumLB.vnEntropy ΩG := by sorry

end SpaceReset.Hardness.Supplement
