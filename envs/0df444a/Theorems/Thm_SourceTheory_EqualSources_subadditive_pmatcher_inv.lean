-- Prove2me | Theorems.Thm_SourceTheory_EqualSources_subadditive_pmatcher_inv
-- name    : SourceTheory.EqualSources.subadditive_pmatcher_inv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:08.947515+00:00
-- url     : https://prove2.me/theorems/d74951e9-a37b-45eb-9414-78ab1d7008d9
-- title:
--   Proof of Theorem 4, p. 8780 — if C is more insensitive than A with a regular region, φ⁻¹(p + ε) − φ⁻¹(p) ≤ φ⁻¹(ε) on [0, 1/2]
-- statement:
--   Let sources $\mathcal A$ and $\mathcal C$ satisfy Assumption 2, and let $\varphi$ be the pmatcher from $\mathcal A$ to $\mathcal C$: a transformation with $w_{\mathcal A}(p) = w_{\mathcal C}(\varphi(p))$ for $p \in [0,1]$. Let $\psi$ be its inverse on $[0,1]$: $\psi(\varphi(p)) = p$ and $\varphi(\psi(p)) = p$ for all $p \in [0,1]$. Let $B, D$ be events such that $[B, D]$ is regular for $\mathcal C$ and $\mathcal C$ is more insensitive than $\mathcal A$ with region $[B, D]$. Then for all $p, \varepsilon \ge 0$ with $p + \varepsilon \le \tfrac12$,
--
--   $$\psi(p+\varepsilon) - \psi(p) \le \psi(\varepsilon).$$
--
--   Together with the corresponding inequality for $\varphi$, this forces the pmatcher to be linear on $[0, \tfrac12]$ in the proof of Theorem 4.
--
--   **Formalization Note.** $\varphi^{-1}$ is a binder $\psi$ with two-sided inverse laws on $[0,1]$, not Lean's junk-valued `Function.invFun`. The paper states the inequality for $p > 0$, $\varepsilon > 0$; the boundary cases hold trivially since $\psi(0) = 0$. Structural Assumption 1 is not needed and is not assumed.
-- source:
--   Baillon et al. (2025), Management Science 71(10), App. B, proof of Theorem 4, p. 8780

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

open Set

namespace SourceTheory.EqualSources

/-- Proof of Theorem 4, p. 8780: if `𝒞` is more insensitive than `𝒜` with an insensitivity region
`[B, D]` that is regular for `𝒞`, the inverse `ψ = φ⁻¹` of the pmatcher `φ` from `𝒜` to `𝒞` satisfies
`ψ(p + ε) − ψ(p) ≤ ψ(ε)` whenever `p, ε ≥ 0` and `p + ε ≤ 1/2`. -/
theorem subadditive_pmatcher_inv {S Γ : Type*} (𝓔 : Set (Set S))
    (pref : (S → Γ) → (S → Γ) → Prop) (U : Γ → ℝ) (W : Set S → ℝ)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (h𝒞 : SourceTheory.Uniform.IsSource 𝓔 W 𝒞)
    (PC PA : Set S → ℝ) (wC wA : ℝ → ℝ) (h2 : SourceTheory.Uniform.Assumption2 pref U W 𝒞 𝒜 PC PA wC wA)
    (B D : Set S) (hB : B ∈ 𝓔) (hD : D ∈ 𝓔)
    (hreg : SourceTheory.Uniform.IsRegularRegion W 𝒞 B D) (hins : SourceTheory.Uniform.IsMoreInsensitive W 𝒞 𝒜 B D)
    (φ ψ : ℝ → ℝ) (hφ : SourceTheory.Uniform.IsTransformation φ) (hφA : ∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p))
    (hψ : ∀ p ∈ Icc (0 : ℝ) 1, ψ (φ p) = p ∧ φ (ψ p) = p) :
    ∀ p ε : ℝ, 0 ≤ p → 0 ≤ ε → p + ε ≤ 1 / 2 → ψ (p + ε) - ψ p ≤ ψ ε := by sorry

end SourceTheory.EqualSources
