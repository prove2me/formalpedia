-- Prove2me | Theorems.Thm_RSSubspaceDesign_theorem_4_4
-- name    : RSSubspaceDesign.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:23:37.955266+00:00
-- url     : https://prove2.me/theorems/1dbfc2fb-d6e6-4dd6-b3a8-9b16b50bd089
-- title:
--   Theorem 4.4 — from extension-field ranks to dimensions
-- statement:
--   Let $E_0\subseteq E_1$ be fields, $C$ an $E_0$-subspace of an $E_1$-vector space, and $H_1,\dots,H_n$ $E_0$-subspaces of $C$. Let $r\ge1$ and $\tau\ge0$. Suppose every nonzero $E_0$-subspace $W\subseteq C$ with $\dim_{E_0}W\le r$ satisfies
--   $$\sum_{i=1}^n\dim_{E_1}\operatorname{span}_{E_1}(W\cap H_i)\;\le\;n\tau\,\dim_{E_1}\operatorname{span}_{E_1}W.\qquad(4.3)$$
--   Then every $E_0$-subspace $U\subseteq C$ of dimension $1\le d\le r$ satisfies
--   $$\sum_{i=1}^n\dim_{E_0}(U\cap H_i)\;\le\;n\tau d.$$
--
--   With $E_1=K(X)$, $E_0=K$ it turns Proposition 4.3 into Theorem 4.2; with $E_1=K$, $E_0=K_0$ it gives Lemma 4.5.
--
--   Differences from the source:
--   - encoding: fields E₀ ⊆ E₁ → fields with an algebra E₀ → E₁ and an E₁-space V carrying the compatible E₀-structure (IsScalarTower); reason: a field homomorphism is injective, so this identifies E₀ with a subfield of E₁; same instances up to isomorphism
--   - encoding: nonzero W ⊆ C with dim_{E₀} W ≤ r → W ≠ ⊥, FiniteDimensional E₀ W and finrank ≤ r; reason: Mathlib's finrank is 0 on infinite-dimensional spaces; the paper's dimension ≤ r means finite dimension
--   - encoding: U ⊆ C of dimension 1 ≤ d ≤ r → 1 ≤ finrank E₀ U ≤ r, with d = finrank E₀ U; reason: finrank ≥ 1 forces finite dimension
--   - encoding: H₁, …, Hₙ → H : Fin n → Submodule E₀ V; reason: Lean convention
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Theorem 4.4, p.20 (PDF p.22), display (4.3)

import Mathlib

namespace RSSubspaceDesign

/-- **Theorem 4.4 (From extension-field ranks to dimensions).** Alrabiah–Goyal–Guruswami,
arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 4.4 with display (4.3), p.20.

Let `E₀ ⊆ E₁` be fields, `C` an `E₀`-subspace of an `E₁`-vector space, and `H₁, …, Hₙ`
`E₀`-subspaces of `C`. Let `r ≥ 1` and `τ ≥ 0`. Suppose every nonzero `E₀`-subspace `W ⊆ C` with
`dim_{E₀} W ≤ r` satisfies
`∑ᵢ dim_{E₁} span_{E₁}(W ∩ Hᵢ) ≤ n τ dim_{E₁} span_{E₁} W` (4.3).
Then every `E₀`-subspace `U ⊆ C` of dimension `1 ≤ d ≤ r` satisfies `∑ᵢ dim_{E₀}(U ∩ Hᵢ) ≤ n τ d`.

**Formalization Note.** Same tower encoding as Lemma 4.6. "`dim_{E₀} W ≤ r`" in the hypothesis is
`FiniteDimensional` plus `finrank ≤ r`, so (4.3) is only demanded of genuinely finite-dimensional
`W`; in the conclusion `1 ≤ finrank` already forces finite dimension. Indices are `Fin n`. -/
theorem theorem_4_4 {E₀ E₁ V : Type*} [Field E₀] [Field E₁] [Algebra E₀ E₁] [AddCommGroup V]
    [Module E₁ V] [Module E₀ V] [IsScalarTower E₀ E₁ V]
    (C : Submodule E₀ V) {n : ℕ} (H : Fin n → Submodule E₀ V) (hH : ∀ i, H i ≤ C)
    (r : ℕ) (hr : 1 ≤ r) (τ : ℝ) (hτ : 0 ≤ τ)
    (hyp : ∀ W : Submodule E₀ V, W ≤ C → W ≠ ⊥ → FiniteDimensional E₀ W →
      Module.finrank E₀ W ≤ r →
      (∑ i, (Module.finrank E₁ (Submodule.span E₁ ((W ⊓ H i : Submodule E₀ V) : Set V)) : ℝ)) ≤
        n * τ * (Module.finrank E₁ (Submodule.span E₁ (W : Set V)) : ℝ)) :
    ∀ U : Submodule E₀ V, U ≤ C → 1 ≤ Module.finrank E₀ U → Module.finrank E₀ U ≤ r →
      (∑ i, (Module.finrank E₀ ↥(U ⊓ H i) : ℝ)) ≤ n * τ * Module.finrank E₀ U := by sorry

end RSSubspaceDesign
