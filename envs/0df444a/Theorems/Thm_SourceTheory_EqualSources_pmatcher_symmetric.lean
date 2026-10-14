-- Prove2me | Theorems.Thm_SourceTheory_EqualSources_pmatcher_symmetric
-- name    : SourceTheory.EqualSources.pmatcher_symmetric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:03.563059+00:00
-- url     : https://prove2.me/theorems/59cc464c-12a2-4719-9526-eea7d4428bc9
-- title:
--   Proof of Theorem 4, p. 8780 — for equally preferred sources the pmatcher satisfies φ(p) + φ(1 − p) = 1, hence φ(1/2) = 1/2
-- statement:
--   Let sources $\mathcal A$ and $\mathcal C$ satisfy Assumption 2: both are uniform, with a-neutral probability measures $P_{\mathcal A}$, $P_{\mathcal C}$ and source functions $w_{\mathcal A}$, $w_{\mathcal C}$. Let $\varphi$ be the pmatcher from $\mathcal A$ to $\mathcal C$: a transformation (continuous, strictly increasing, $\varphi(0) = 0$, $\varphi(1) = 1$) with $w_{\mathcal A}(p) = w_{\mathcal C}(\varphi(p))$ for all $p \in [0,1]$. If $\mathcal A$ and $\mathcal C$ are equally preferred ($\mathcal C$ is preferred to $\mathcal A$ and $\mathcal A$ is preferred to $\mathcal C$), then
--
--   $$\varphi(p) + \varphi(1-p) = 1 \quad \text{for all } p \in [0,1], \qquad \varphi(\tfrac12) = \tfrac12.$$
--
--   Twofold source preference in both directions therefore makes the pmatcher symmetric about $(\tfrac12, \tfrac12)$, which reduces the proof of Theorem 4 to the interval $[0, \tfrac12]$.
--
--   **Formalization Note.** The pmatcher (18) is a binder $\varphi$ with the defining identity, not an inverse function. Structural Assumption 1 is not needed and is not assumed.
-- source:
--   Baillon et al. (2025), Management Science 71(10), App. B, proof of Theorem 4, p. 8780

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

open Set

namespace SourceTheory.EqualSources

/-- Proof of Theorem 4, p. 8780: if `𝒜` and `𝒞` are equally preferred and `φ` is the pmatcher from `𝒜`
to `𝒞` (`w_𝒜 = w_𝒞 ∘ φ`), then `φ(p) + φ(1 − p) = 1` on `[0, 1]`, hence `φ(1/2) = 1/2`. -/
theorem pmatcher_symmetric {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (h𝒞 : SourceTheory.Uniform.IsSource 𝓔 W 𝒞)
    (PC PA : Set S → ℝ) (wC wA : ℝ → ℝ) (h2 : SourceTheory.Uniform.Assumption2 pref U W 𝒞 𝒜 PC PA wC wA)
    (hpref : SourceTheory.Uniform.IsPreferredTo W 𝒞 𝒜) (hpref' : SourceTheory.Uniform.IsPreferredTo W 𝒜 𝒞)
    (φ : ℝ → ℝ) (hφ : SourceTheory.Uniform.IsTransformation φ) (hφA : ∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p)) :
    (∀ p ∈ Icc (0 : ℝ) 1, φ p + φ (1 - p) = 1) ∧ φ (1 / 2) = 1 / 2 := by sorry

end SourceTheory.EqualSources
