-- Prove2me | Theorems.Thm_RSSubspaceDesign_lemma_4_6
-- name    : RSSubspaceDesign.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:23:34.037199+00:00
-- url     : https://prove2.me/theorems/b6b0d3b4-ce1d-4747-bd4a-e7e70d678c13
-- title:
--   Lemma 4.6 — dimension comparison: a chain $0=U_0\subsetneq\dots\subsetneq U_h=U$ with weights $a_\ell\ge0$
-- statement:
--   Let $E_0\subseteq E_1$ be fields and $U$ a finite-dimensional $E_0$-subspace of an $E_1$-vector space. For $S\subseteq U$ write $\rho(S)=\dim_{E_1}\operatorname{span}_{E_1}S$. Then there are spaces
--   $$0=U_0\subsetneq U_1\subsetneq\dots\subsetneq U_h=U,\qquad U_i=U\cap\operatorname{span}_{E_1}U_i\quad(i=0,\dots,h),$$
--   and nonnegative real numbers $a_1,\dots,a_h$ such that, for every $E_0$-subspace $S\subseteq U$,
--   $$\dim_{E_0}S\;\le\;\sum_{\ell=1}^h a_\ell\,\rho(S\cap U_\ell),\qquad \sum_{\ell=1}^h a_\ell\,\rho(U_\ell)=\dim_{E_0}U.$$
--
--   This is the key step of the transfer Theorem 4.4: dimensions over the small field are controlled by a nonnegative combination of ranks over the large field.
--
--   Differences from the source:
--   - encoding: fields E₀ ⊆ E₁ → fields with an algebra E₀ → E₁ and an E₁-space V carrying the compatible E₀-structure (IsScalarTower); reason: a field homomorphism is injective, so this identifies E₀ with a subfield of E₁; same instances up to isomorphism
--   - encoding: the chain U₀ ⊊ ⋯ ⊊ U_h and weights a₁, …, a_h (ℓ = 1, …, h) → a strictly increasing Us : Fin (h + 1) → Submodule E₀ V and a : Fin h → ℝ; index ℓ ↦ ℓ.succ; reason: Lean convention; same data
--   - encoding: ρ(S) = dim_{E₁} span_{E₁} S → Module.finrank E₁ (Submodule.span E₁ S); reason: the spans are finite-dimensional since U is
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Lemma 4.6, p.21 (PDF p.23)

import Mathlib

namespace RSSubspaceDesign

/-- **Lemma 4.6 (Dimension comparison).** Alrabiah–Goyal–Guruswami, arXiv:2610.36215 (held
version, sha256 cf26424b…f36206), Lemma 4.6, p.21.

Let `E₀ ⊆ E₁` be fields and `U` a finite-dimensional `E₀`-subspace of an `E₁`-vector space. For
`S ⊆ U` write `ρ(S) = dim_{E₁} span_{E₁} S`. There are spaces `0 = U₀ ⊊ U₁ ⊊ ⋯ ⊊ U_h = U` with
`Uᵢ = U ∩ span_{E₁} Uᵢ` for all `i ∈ {0, …, h}`, and nonnegative reals `a₁, …, a_h`, such that for
every `E₀`-subspace `S ⊆ U`, `dim_{E₀} S ≤ ∑_{ℓ=1}^h a_ℓ ρ(S ∩ U_ℓ)`, and
`∑_{ℓ=1}^h a_ℓ ρ(U_ℓ) = dim_{E₀} U`.

**Formalization Note.** `E₀ ⊆ E₁` is an algebra `E₀ → E₁`, and the ambient space `V` is an
`E₁`-module with the compatible `E₀`-structure (`IsScalarTower E₀ E₁ V`). The chain is
`Us : Fin (h + 1) → Submodule E₀ V`, strictly increasing; the weights are `a : Fin h → ℝ`, and the
paper's index `ℓ = 1, …, h` is `ℓ.succ` for `ℓ : Fin h`. -/
theorem lemma_4_6 {E₀ E₁ V : Type*} [Field E₀] [Field E₁] [Algebra E₀ E₁] [AddCommGroup V]
    [Module E₁ V] [Module E₀ V] [IsScalarTower E₀ E₁ V]
    (U : Submodule E₀ V) [FiniteDimensional E₀ U] :
    ∃ (h : ℕ) (Us : Fin (h + 1) → Submodule E₀ V) (a : Fin h → ℝ),
      Us 0 = ⊥ ∧ Us (Fin.last h) = U ∧ StrictMono Us ∧
      (∀ i, Us i = U ⊓ (Submodule.span E₁ (Us i : Set V)).restrictScalars E₀) ∧
      (∀ ℓ, 0 ≤ a ℓ) ∧
      (∀ S : Submodule E₀ V, S ≤ U →
        (Module.finrank E₀ S : ℝ) ≤
          ∑ ℓ : Fin h, a ℓ *
            (Module.finrank E₁ (Submodule.span E₁ ((S ⊓ Us ℓ.succ : Submodule E₀ V) : Set V)) : ℝ)) ∧
      ∑ ℓ : Fin h, a ℓ * (Module.finrank E₁ (Submodule.span E₁ (Us ℓ.succ : Set V)) : ℝ) =
        Module.finrank E₀ U := by sorry

end RSSubspaceDesign
