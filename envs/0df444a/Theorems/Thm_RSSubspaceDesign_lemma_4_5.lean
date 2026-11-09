-- Prove2me | Theorems.Thm_RSSubspaceDesign_lemma_4_5
-- name    : RSSubspaceDesign.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:25:27.202552+00:00
-- url     : https://prove2.me/theorems/1b2e06b3-29f5-4a39-83c2-896c5968b92a
-- title:
--   Lemma 4.5 — subspace designs transfer to subfields
-- statement:
--   Let $K_0\subseteq K$ be finite fields. If a $K$-additive code $C\subseteq\Sigma^n$ is a $\tau$-subspace design over $K$, then it is also a $\tau$-subspace design over $K_0$.
--
--   Together with Theorem 4.2 over a quadratic extension of the input field, this gives the "every subfield" clause of Theorem 1.1.
--
--   Differences from the source:
--   - generalization: alphabet Σ = K^s → any K-module V with a compatible K₀-structure (IsScalarTower K₀ K V); reason: Σ = K^s is the special case V = K^s; the proof (Theorem 4.4 with E₁ = K) uses only the K-module structure
--   - generalization: τ : ℤ≥1 → [0, 1] nondecreasing → any τ : ℕ → ℝ; reason: every τ of the paper is such a function; the claim for all τ specializes to the paper's
--   - encoding: K₀ ⊆ K finite fields → fields with an algebra K₀ → K, K finite; reason: a field homomorphism is injective, so this identifies K₀ with a subfield of K; K₀ is then finite
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Lemma 4.5, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_RSSubspaceDesign_IsSubspaceDesign

namespace RSSubspaceDesign

/-- **Lemma 4.5 (Subspace-design transfers to subfields).** Alrabiah–Goyal–Guruswami,
arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Lemma 4.5, p.20.

Let `K₀ ⊆ K` be finite fields. If a `K`-additive code `C ⊆ Σⁿ` is a `τ`-subspace design over `K`,
then it is also a `τ`-subspace design over `K₀`.

**Formalization Note.** `K₀ ⊆ K` is any field `K₀` with an algebra `K₀ → K` (every subfield, via
its inclusion; `K₀` is finite because it embeds in `K`). The alphabet `Σ` (written `V`) is any
`K`-module with the compatible `K₀`-structure, which includes the paper's `Σ = Kˢ`. `τ : ℕ → ℝ` is
not required to be nondecreasing or `[0, 1]`-valued (see `IsSubspaceDesign`). `C` viewed over `K₀`
is `C.restrictScalars K₀`. -/
theorem lemma_4_5 {K₀ K V : Type*} [Field K₀] [Field K] [Finite K] [Algebra K₀ K]
    [AddCommGroup V] [Module K V] [Module K₀ V] [IsScalarTower K₀ K V]
    {n : ℕ} (C : Submodule K (Fin n → V)) (τ : ℕ → ℝ) (hC : IsSubspaceDesign K C τ) :
    IsSubspaceDesign K₀ (C.restrictScalars K₀) τ := by sorry

end RSSubspaceDesign
