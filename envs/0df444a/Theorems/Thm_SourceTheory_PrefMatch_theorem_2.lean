-- Prove2me | Theorems.Thm_SourceTheory_PrefMatch_theorem_2
-- name    : SourceTheory.PrefMatch.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:11.049802+00:00
-- url     : https://prove2.me/theorems/5788f506-6df3-4d9b-9853-7f8eeb076404
-- title:
--   Theorem 2, p. 8775 — 𝒞 is preferred to 𝒜 iff w_𝒜 = w_𝒞 ∘ φ for a disliked transformation φ
-- statement:
--   Assume structural Assumption 1 (biseparable utility with convex-ranged weighting function $W$, strong monotonicity, cumulative dominance and the Archimedean axiom) and Assumption 2: $\mathcal C$ and $\mathcal A$ are sources that are uniform, with a-neutral probability measures $P_{\mathcal C}$, $P_{\mathcal A}$ and source functions $w_{\mathcal C}$, $w_{\mathcal A}$, so $W = w_{\mathcal C} \circ P_{\mathcal C}$ on $\mathcal C$ and $W = w_{\mathcal A} \circ P_{\mathcal A}$ on $\mathcal A$. Then the following are equivalent:
--   1. $\mathcal C$ is preferred to $\mathcal A$: for all $C_1 \in \mathcal C$, $A_1 \in \mathcal A$, $W(A_1) = W(C_1) \implies W(A_1^c) \le W(C_1^c)$;
--   2. there exists a disliked transformation $\varphi$ such that
--
--   $$w_{\mathcal A} = w_{\mathcal C} \circ \varphi \quad \text{on } [0,1],$$
--
--   where *disliked* means $\varphi(p) \le 1 - \varphi(1-p)$ for all $p \in [0,1]$.
--
--   Source preference captures ambiguity aversion, the competence effect and home bias; the theorem shows that it is exactly dislike of the pmatcher $\varphi$, the map sending the a-neutral probability of an event of $\mathcal A$ to that of an equally preferred event of $\mathcal C$. With $\mathcal C$ the risky source, $\varphi$ is the matching-probability function of the experimental literature.
--
--   **Formalization Note.** "Transformation" is not defined in the paper; it is read as a continuous, strictly increasing $\varphi : [0,1] \to [0,1]$ with $\varphi(0) = 0$, $\varphi(1) = 1$, the properties the paper attributes to the pmatcher in (18). Since $w_{\mathcal C}$ is a bijection of $[0,1]$, any map of $[0,1]$ into $[0,1]$ with $w_{\mathcal A} = w_{\mathcal C} \circ \varphi$ is this pmatcher, so the reading loses no instance. Events form an algebra; each source is a subalgebra on which $W$ is convex ranged; twofold partitions are $(A_1, A_1^c)$.
-- source:
--   Baillon et al. (2025), Management Science 71(10), Theorem 2, p. 8775

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.PrefMatch

open Set SourceTheory.Uniform

/-- Theorem 2 (p. 8775): under structural Assumption 1 and Assumption 2, `𝒞` is preferred to
`𝒜` iff there exists a disliked transformation `φ` with `w_𝒜 = w_𝒞 ∘ φ` (on `[0, 1]`). -/
theorem theorem_2 {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : IsSource 𝓔 W 𝒜) (h𝒞 : IsSource 𝓔 W 𝒞)
    (PC PA : Set S → ℝ) (wC wA : ℝ → ℝ) (h2 : Assumption2 pref U W 𝒞 𝒜 PC PA wC wA) :
    IsPreferredTo W 𝒞 𝒜 ↔
      ∃ φ : ℝ → ℝ, IsTransformation φ ∧ IsDisliked φ ∧ ∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p) := by sorry

end SourceTheory.PrefMatch
