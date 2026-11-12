-- Prove2me | Theorems.Thm_QSampVerif_lemma_12_14
-- name    : QSampVerif.lemma_12_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:31:54.383196+00:00
-- url     : https://prove2.me/theorems/3cbc3ba3-5e5d-43b0-b514-003e4b33835f
-- title:
--   Lemma 12.14 — polarization and physical tests: $|\mathrm{Tr}[MC(\Phi_0-\Phi_1)(A\xi B^\dagger)D^\dagger]|\le\sum_{z,w}\eta_{z,w}$
-- statement:
--   Let $\mathcal H_0,\dots,\mathcal H_3$ be finite-dimensional. Let $\xi$ be a density operator on $\mathcal H_0$, $M$ an effect on $\mathcal H_3$ ($0\preceq M\preceq I$), $A,B:\mathcal H_0\to\mathcal H_1$ and $C,D:\mathcal H_2\to\mathcal H_3$ contractions, and $\Phi_0,\Phi_1:\mathcal L(\mathcal H_1)\to\mathcal L(\mathcal H_2)$ quantum channels. For $z,w\in\mathcal Z=\{1,i,-1,-i\}$ let
--
--   $$p_{b,z,w}=\mathrm{Tr}\Bigl[M\,\tfrac{C+wD}{2}\,\Phi_b\Bigl(\tfrac{A+zB}{2}\,\xi\,\bigl(\tfrac{A+zB}{2}\bigr)^\dagger\Bigr)\bigl(\tfrac{C+wD}{2}\bigr)^\dagger\Bigr].\qquad(391)$$
--
--   If $\eta_{z,w}\ge0$ satisfy $|p_{0,z,w}-p_{1,z,w}|\le\eta_{z,w}$ for all $z,w\in\mathcal Z$, then
--
--   1. every $p_{b,z,w}$ is a real number with $0\le p_{b,z,w}\le1$;
--   2. $$\bigl|\mathrm{Tr}[MC(\Phi_0-\Phi_1)(A\xi B^\dagger)D^\dagger]\bigr|\le\sum_{z,w\in\mathcal Z}\eta_{z,w}.$$
--
--   The lemma expresses a cross-term comparison through sixteen physical experiments, so that a hiding guarantee for physical tests bounds the cross terms of the RSP expansion.
--
--   **Formalization Note** A contraction is $A^\dagger A\preceq I$; a channel has a normalized Kraus family. $\mathcal Z$ is enumerated as $i^k$, $k=0,\dots,3$, and $|\cdot|$ is the complex modulus.
--
--   Differences from the source:
--   - generalization: ξ, M efficiently implementable; A, B, C, D accepted branches of efficient unitary realizations with common retained environments → no efficiency or realization assumption: any density operator, effect, contractions and channels; reason: the identity (392) and both conclusions hold for all contractions and channels; the dropped assumptions only serve to apply the hiding guarantee elsewhere, and the Lean statement specializes to the printed one
--   - encoding: contraction; channel; z, w ∈ 𝒵; 0 ≤ p_{b,z,w} ≤ 1 → (1 − A†A).PosSemidef; published IsChannel (normalized Kraus family); k, l ∈ Fin 4 with z = i^k; Im p = 0 ∧ 0 ≤ Re p ≤ 1; reason: same objects and the same claim (p is a complex trace)
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Lemma 12.14, (391), pp.142–143 (PDF 143–144)

import Definitions.Def_QSampVerif_physTest

set_option autoImplicit false

namespace QSampVerif

open QAlgorithms
open scoped Matrix ComplexOrder

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7),
Lemma 12.14 (Polarization and physical tests), pp.142–143 (PDF 143–144).

For finite-dimensional `H₀, …, H₃`, a density operator `ξ` on `H₀`, an effect `0 ⪯ M ⪯ I` on
`H₃`, contractions `A, B : H₀ → H₁` and `C, D : H₂ → H₃`, and channels `Φ₀, Φ₁ : L(H₁) → L(H₂)`,
let `p_{b,z,w}` be the physical tests (391). If `η_{z,w} ≥ 0` and
`|p_{0,z,w} − p_{1,z,w}| ≤ η_{z,w}` for all `z, w ∈ Z`, then every `p_{b,z,w}` is a real number in
`[0, 1]` and `|Tr[M C (Φ₀ − Φ₁)(A ξ B†) D†]| ≤ Σ_{z,w ∈ Z} η_{z,w}`.

**Formalization Note.** A contraction is `A†A ⪯ I`; a channel is a map with a normalized Kraus
family (the published `IsChannel`); `Z = {i^k : k = 0, …, 3}`. -/
theorem lemma_12_14 {ι₀ ι₁ ι₂ ι₃ : Type*} [Fintype ι₀] [DecidableEq ι₀] [Fintype ι₁]
    [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] [Fintype ι₃] [DecidableEq ι₃]
    (ξ : Matrix ι₀ ι₀ ℂ) (hξ : ξ.PosSemidef) (hξtr : ξ.trace = 1)
    (M : Matrix ι₃ ι₃ ℂ) (hM : M.PosSemidef) (hMI : (1 - M).PosSemidef)
    (A B : Matrix ι₁ ι₀ ℂ) (hA : (1 - Aᴴ * A).PosSemidef) (hB : (1 - Bᴴ * B).PosSemidef)
    (C D : Matrix ι₃ ι₂ ℂ) (hC : (1 - Cᴴ * C).PosSemidef) (hD : (1 - Dᴴ * D).PosSemidef)
    (Φ : Bool → Superop ι₁ ι₂) (hΦ : ∀ b, IsChannel (Φ b))
    (η : Fin 4 → Fin 4 → ℝ) (hη : ∀ k l, 0 ≤ η k l)
    (hp : ∀ k l, ‖physTest M C D (Φ false) A B ξ (zPhase k) (zPhase l) -
      physTest M C D (Φ true) A B ξ (zPhase k) (zPhase l)‖ ≤ η k l) :
    (∀ b k l, (physTest M C D (Φ b) A B ξ (zPhase k) (zPhase l)).im = 0 ∧
      0 ≤ (physTest M C D (Φ b) A B ξ (zPhase k) (zPhase l)).re ∧
      (physTest M C D (Φ b) A B ξ (zPhase k) (zPhase l)).re ≤ 1) ∧
    ‖Matrix.trace (M * C * (Φ false (A * ξ * Bᴴ) - Φ true (A * ξ * Bᴴ)) * Dᴴ)‖ ≤
      ∑ k, ∑ l, η k l := by sorry

end QSampVerif
