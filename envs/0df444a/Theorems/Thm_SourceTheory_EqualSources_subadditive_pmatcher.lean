-- Prove2me | Theorems.Thm_SourceTheory_EqualSources_subadditive_pmatcher
-- name    : SourceTheory.EqualSources.subadditive_pmatcher
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:24.839377+00:00
-- url     : https://prove2.me/theorems/14157a02-05e3-42ed-8a6f-ea4730dad0c0
-- title:
--   Proof of Theorem 4, p. 8780 — if A is more insensitive than C with a regular region, φ(p + ε) − φ(p) ≤ φ(ε) on [0, 1/2]
-- statement:
--   Let sources $\mathcal A$ and $\mathcal C$ satisfy Assumption 2 (uniform, with a-neutral probabilities $P_{\mathcal A}$, $P_{\mathcal C}$ and source functions $w_{\mathcal A}$, $w_{\mathcal C}$), and let $\varphi$ be the pmatcher from $\mathcal A$ to $\mathcal C$: a transformation with $w_{\mathcal A}(p) = w_{\mathcal C}(\varphi(p))$ for $p \in [0,1]$. Let $B, D$ be events such that $[B, D]$ is regular for $\mathcal A$ and $\mathcal A$ is more insensitive than $\mathcal C$ with region $[B, D]$. Then for all $p, \varepsilon \ge 0$ with $p + \varepsilon \le \tfrac12$,
--
--   $$\varphi(p+\varepsilon) - \varphi(p) \le \varphi(\varepsilon).$$
--
--   This is half of the functional inequalities that force the pmatcher to be linear on $[0, \tfrac12]$ in the proof of Theorem 4.
--
--   **Formalization Note.** The paper states the inequality for $p > 0$ and $\varepsilon > 0$; the cases $p = 0$ or $\varepsilon = 0$ hold trivially because $\varphi(0) = 0$, so the closed form is no stronger. Structural Assumption 1 is not needed and is not assumed; only the regularity for $\mathcal A$ and the insensitivity of $\mathcal A$ relative to $\mathcal C$ are used.
-- source:
--   Baillon et al. (2025), Management Science 71(10), App. B, proof of Theorem 4, p. 8780

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

open Set

namespace SourceTheory.EqualSources

/-- Proof of Theorem 4, p. 8780: if `𝒜` is more insensitive than `𝒞` with an insensitivity region
`[B, D]` that is regular for `𝒜`, the pmatcher `φ` from `𝒜` to `𝒞` satisfies
`φ(p + ε) − φ(p) ≤ φ(ε)` whenever `p, ε ≥ 0` and `p + ε ≤ 1/2`. -/
theorem subadditive_pmatcher {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (h𝒞 : SourceTheory.Uniform.IsSource 𝓔 W 𝒞)
    (PC PA : Set S → ℝ) (wC wA : ℝ → ℝ) (h2 : SourceTheory.Uniform.Assumption2 pref U W 𝒞 𝒜 PC PA wC wA)
    (B D : Set S) (hB : B ∈ 𝓔) (hD : D ∈ 𝓔)
    (hreg : SourceTheory.Uniform.IsRegularRegion W 𝒜 B D) (hins : SourceTheory.Uniform.IsMoreInsensitive W 𝒜 𝒞 B D)
    (φ : ℝ → ℝ) (hφ : SourceTheory.Uniform.IsTransformation φ) (hφA : ∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p)) :
    ∀ p ε : ℝ, 0 ≤ p → 0 ≤ ε → p + ε ≤ 1 / 2 → φ (p + ε) - φ p ≤ φ ε := by sorry

end SourceTheory.EqualSources
