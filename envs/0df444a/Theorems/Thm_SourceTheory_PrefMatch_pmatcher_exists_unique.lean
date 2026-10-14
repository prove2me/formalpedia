-- Prove2me | Theorems.Thm_SourceTheory_PrefMatch_pmatcher_exists_unique
-- name    : SourceTheory.PrefMatch.pmatcher_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:00.148302+00:00
-- url     : https://prove2.me/theorems/f3ed86c8-5802-4d45-8aed-3268d75b545f
-- title:
--   (18), p. 8775 — the pmatcher φ with w_A = w_C ∘ φ exists, is a continuous strictly increasing transformation, and is unique
-- statement:
--   Assume structural Assumption 1 and Assumption 2: $\mathcal C$ and $\mathcal A$ are sources that are uniform with a-neutral probability measures $P_{\mathcal C}$, $P_{\mathcal A}$ and source functions $w_{\mathcal C}$, $w_{\mathcal A}$. Then there is a transformation $\varphi$ — a continuous, strictly increasing map of $[0,1]$ into $[0,1]$ with $\varphi(0) = 0$ and $\varphi(1) = 1$ — such that
--
--   $$w_{\mathcal A}(p) = w_{\mathcal C}(\varphi(p)) \qquad \text{for all } p \in [0,1],$$
--
--   and every map $\varphi'$ of $[0,1]$ into $[0,1]$ with $w_{\mathcal A} = w_{\mathcal C} \circ \varphi'$ on $[0,1]$ coincides with $\varphi$ on $[0,1]$.
--
--   This $\varphi = w_{\mathcal C}^{-1} \circ w_{\mathcal A}$ is the *pmatcher* from $\mathcal A$ to $\mathcal C$: for an event of $\mathcal A$ with a-neutral probability $p$, $\varphi(p)$ is the a-neutral probability of an equally preferred event of $\mathcal C$. It is the central tool of §8 of the paper.
--
--   **Formalization Note.** The pmatcher is not defined through an inverse function; existence and uniqueness are stated instead. Uniqueness is among maps into $[0,1]$, the domain on which $w_{\mathcal C}$ is constrained.
-- source:
--   Baillon et al. (2025), Management Science 71(10), Equation (18) and the sentence after it, p. 8775

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.PrefMatch

open Set SourceTheory.Uniform

/-- Equation (18) and the sentence after it (p. 8775): the pmatcher `φ` from `𝒜` to `𝒞`, with
`w_𝒜 = w_𝒞 ∘ φ` on `[0, 1]`, exists, is a continuous strictly increasing probability weighting
function, and is the unique map of `[0, 1]` into `[0, 1]` with this property. -/
theorem pmatcher_exists_unique {S Γ : Type*} (𝓔 : Set (Set S))
    (pref : (S → Γ) → (S → Γ) → Prop) (U : Γ → ℝ) (W : Set S → ℝ) (h1 : Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : IsSource 𝓔 W 𝒜) (h𝒞 : IsSource 𝓔 W 𝒞)
    (PC PA : Set S → ℝ) (wC wA : ℝ → ℝ) (h2 : Assumption2 pref U W 𝒞 𝒜 PC PA wC wA) :
    ∃ φ : ℝ → ℝ, IsTransformation φ ∧ (∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p)) ∧
      ∀ φ' : ℝ → ℝ, MapsTo φ' (Icc 0 1) (Icc 0 1) → (∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ' p)) →
        ∀ p ∈ Icc (0 : ℝ) 1, φ' p = φ p := by sorry

end SourceTheory.PrefMatch
