-- Prove2me | Theorems.Thm_SelectiveDPT_lemma_3_2
-- name    : SelectiveDPT.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:51:02.637742+00:00
-- url     : https://prove2.me/theorems/a82a3a70-bc8d-45d5-9123-c2ec27fe9a0d
-- title:
--   Lemma 3.2 — $\mathrm{Tr}[\Pi_{\Gamma^\pm,\ge\lambda^\pm}\sigma_y] \le 1/(1+\lambda^\pm)$
-- statement:
--   Let $f : D \to Y$, let $\mu$ be a distribution on $D$, let $\Gamma^\pm$ be a witness to Proposition 2.5 for computing $f$ under $\mu$, and let $-1 < \lambda^\pm < 1$. Let $y \in Y$ and let $\psi = \sum_{x : f(x) = y}\beta_x |x\rangle$ be a unit vector in $\mathbb C^D$ supported on $f^{-1}(y)$, so that $\sigma_y = |\psi\rangle\langle\psi| \in S_y$. Then
--   $$\mathrm{Tr}\big[\Pi_{\Gamma^\pm,\ge\lambda^\pm}\,\sigma_y\big] = \langle\psi|\Pi_{\Gamma^\pm,\ge\lambda^\pm}|\psi\rangle \le \frac{1}{1+\lambda^\pm} .$$
--
--   It is the first step in extracting the parameters $(\lambda,\eta)$ of a multiplicative witness from a negative-weights witness.
--
--   Differences from the source:
--   - reading: σ_y ∈ S_y = {|ψ_y⟩⟨ψ_y| : |ψ_y⟩ = Σ_{x: f(x)=y} β_x|x⟩}, no normalization printed → ψ a unit vector supported on f⁻¹(y); reason: the σ_y are input states (p.18) and the proof uses ⟨ϕ_y|ϕ_y⟩ = 1; without the normalization the bound fails by scaling
--   - encoding: Tr[Π σ_y] → the real part of ⟨ψ, Π ψ⟩; reason: Tr[Π|ψ⟩⟨ψ|] = ⟨ψ|Π|ψ⟩, which is real for a Hermitian Π
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Lemma 3.2 and the definition of S_y, S_f, p.19

import Mathlib
import Definitions.Def_SelectiveDPT_IsNegAdvWitness
import Definitions.Def_SelectiveDPT_projLe

open Matrix

namespace SelectiveDPT

/-- Lemma 3.2 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), p.19: let `Γ±` be any witness to
Proposition 2.5 for computing `f` under the distribution `D` and let `−1 < λ± < 1`. Let
`σ_y ∈ S_f`. Then `Tr[Π_{Γ±,≥λ±} σ_y] ≤ 1/(1 + λ±)`. Here
`S_y = {|ψ_y⟩⟨ψ_y| : |ψ_y⟩ = Σ_{x : f(x) = y} β_x |x⟩}` and `S_f = ⋃_y S_y` (p.19).

**Formalization Note.** `σ_y = |ψ⟩⟨ψ|` for a unit vector `ψ` on `ℂ^D` supported on `f⁻¹(y)`, so
`Tr[Π σ_y] = ⟨ψ|Π|ψ⟩`. The unit norm is the reading of "input state" (p.18); the proof uses
`⟨ψ|ψ⟩ = 1`. -/
theorem lemma_3_2 {ι Y : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} [NeZero d]
    (D : Finset (ι → ZMod d)) (μ : (ι → ZMod d) → ℝ) (hμ : IsDistOn μ D)
    (f : (ι → ZMod d) → Y) (Γ : Matrix D D ℂ) (hΓ : IsNegAdvWitness μ D f Γ) (lam : ℝ)
    (hlam₀ : -1 < lam) (hlam₁ : lam < 1) (y : Y) (ψ : D → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hsupp : ∀ x : D, f x.1 ≠ y → ψ x = 0) :
    (star ψ ⬝ᵥ (projGe Γ lam *ᵥ ψ)).re ≤ 1 / (1 + lam) := by sorry

end SelectiveDPT
