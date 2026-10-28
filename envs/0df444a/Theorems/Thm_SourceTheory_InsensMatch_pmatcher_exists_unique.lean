-- Prove2me | Theorems.Thm_SourceTheory_InsensMatch_pmatcher_exists_unique
-- name    : SourceTheory.InsensMatch.pmatcher_exists_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:13.37883+00:00
-- url     : https://prove2.me/theorems/93b8a245-2ca4-4494-9fbc-dc134992556e
-- title:
--   (18), p. 8775 — the pmatcher φ with w_A = w_C ∘ φ exists, is continuous and strictly increasing, and is unique
-- statement:
--   Assume structural Assumption 1 and Assumption 2 for sources $\mathcal C$ and $\mathcal A$, with a-neutral probabilities $P_{\mathcal C}$, $P_{\mathcal A}$ and source functions $w_{\mathcal C}$, $w_{\mathcal A}$. Then there is a transformation $\varphi$ (a continuous, strictly increasing map of $[0,1]$ into $[0,1]$ with $\varphi(0)=0$, $\varphi(1)=1$) such that
--
--   $$w_{\mathcal A}(p) = w_{\mathcal C}(\varphi(p)) \quad \text{for all } p \in [0,1],$$
--
--   i.e. $\varphi = w_{\mathcal C}^{-1} \circ w_{\mathcal A}$ as in (18). Moreover $\varphi$ is unique: any map $\varphi'$ of $[0,1]$ into $[0,1]$ with $w_{\mathcal A} = w_{\mathcal C} \circ \varphi'$ on $[0,1]$ agrees with $\varphi$ on $[0,1]$.
--
--   The map $\varphi$ is the *pmatcher* from $\mathcal A$ to $\mathcal C$: for an event $A$ of $\mathcal A$ with a-neutral probability $p$, $\varphi(p)$ is the a-neutral probability of an equally preferred event of $\mathcal C$. Theorems 2–4 express all comparative uncertainty attitudes through it.
--
--   **Formalization Note.** The pmatcher is not defined through an inverse function (a Lean inverse would take junk values off the range); it is asserted to exist, with the composite identity on $[0,1]$.
-- source:
--   Baillon et al. (2025), Management Science 71(10), (18) and the following paragraph, p. 8775

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.InsensMatch

open Set

/-- Equation (18) and the sentence after it (p. 8775): the pmatcher `φ` from `𝒜` to `𝒞`, with
`w_𝒜 = w_𝒞 ∘ φ` on `[0, 1]`, exists, is a continuous strictly increasing probability weighting
function, and is the unique map of `[0, 1]` into `[0, 1]` with this property. -/
theorem pmatcher_exists_unique {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : SourceTheory.Uniform.Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (h𝒞 : SourceTheory.Uniform.IsSource 𝓔 W 𝒞)
    (PC PA : Set S → ℝ) (wC wA : ℝ → ℝ) (h2 : SourceTheory.Uniform.Assumption2 pref U W 𝒞 𝒜 PC PA wC wA) :
    ∃ φ : ℝ → ℝ, SourceTheory.Uniform.IsTransformation φ ∧ (∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p)) ∧
      ∀ φ' : ℝ → ℝ, MapsTo φ' (Icc 0 1) (Icc 0 1) → (∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ' p)) →
        ∀ p ∈ Icc (0 : ℝ) 1, φ' p = φ p := by sorry

end SourceTheory.InsensMatch
