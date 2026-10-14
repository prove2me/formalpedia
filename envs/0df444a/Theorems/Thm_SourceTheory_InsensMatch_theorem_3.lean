-- Prove2me | Theorems.Thm_SourceTheory_InsensMatch_theorem_3
-- name    : SourceTheory.InsensMatch.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:13.033903+00:00
-- url     : https://prove2.me/theorems/97854bea-b457-46a2-bdb7-2a2504ab454f
-- title:
--   Theorem 3, p. 8775 — A is more insensitive than C with region [B, D] iff w_A = w_C ∘ φ for a φ insensitive on [P_A(B), P_A(D)]
-- statement:
--   Assume structural Assumption 1 and Assumption 2: sources $\mathcal C$ and $\mathcal A$ are uniform, with a-neutral probabilities $P_{\mathcal C}$, $P_{\mathcal A}$ and source functions $w_{\mathcal C}$, $w_{\mathcal A}$. Let $B, D \in \mathcal A$ be boundary events from the source $\mathcal A$. Then the following are equivalent:
--   1. $\mathcal A$ is more insensitive than $\mathcal C$ with insensitivity region $[B, D]$ (Definition 4, conditions (8)–(9));
--   2. there exists a transformation $\varphi$ that is insensitive with insensitivity region $[P_{\mathcal A}(B), P_{\mathcal A}(D)]$ (conditions (13)–(14)) such that
--
--   $$w_{\mathcal A} = w_{\mathcal C} \circ \varphi \quad \text{on } [0,1].$$
--
--   This is the paper's third main result. It characterises the cognitive component of comparative uncertainty attitudes, insensitivity (a lack of discriminatory power that overweights extreme events relative to middle events), entirely through the pmatcher $\varphi$ between the two sources: more insensitivity for $\mathcal A$ than for $\mathcal C$ is the same as an inverse-S, insensitive pmatcher, and the insensitivity region of the preference condition is carried to the probability interval $[P_{\mathcal A}(B), P_{\mathcal A}(D)]$. With $\mathcal C$ the risky source, $\varphi$ is the matching-probability function and the theorem characterises ambiguity-generated insensitivity.
--
--   **Formalization Note.** The theorem is stated in the form of its "Furthermore" sentence, which pins both regions: the region of the preference condition is $[B, D]$ with $B, D \in \mathcal A$ and the region of $\varphi$ is exactly $[P_{\mathcal A}(B), P_{\mathcal A}(D)]$. The bare equivalence with both regions existentially quantified would be near-vacuous, since a function region $[b, d]$ with $b > 1$, $d < 0$ makes (13)–(14) empty. The function region is not required to satisfy $0 \le b < d \le 1$, because $P_{\mathcal A}(B) \ge P_{\mathcal A}(D)$ can occur for $B, D \in \mathcal A$. A "transformation" is read as a continuous probability weighting function on $[0,1]$, the properties (18) gives the pmatcher. Each source is a subalgebra of events on which $W$ is convex ranged.
-- source:
--   Baillon et al. (2025), Management Science 71(10), Theorem 3, p. 8775

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.InsensMatch

open Set

/-- Theorem 3 (p. 8775), in its "Furthermore" form: for boundary events `B, D` from `𝒜`,
`𝒜` is more insensitive than `𝒞` with insensitivity region `[B, D]` iff `w_𝒜 = w_𝒞 ∘ φ` on
`[0, 1]` for a transformation `φ` that is insensitive with region `[P_𝒜(B), P_𝒜(D)]`. -/
theorem theorem_3 {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : SourceTheory.Uniform.Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (h𝒞 : SourceTheory.Uniform.IsSource 𝓔 W 𝒞)
    (PC PA : Set S → ℝ) (wC wA : ℝ → ℝ) (h2 : SourceTheory.Uniform.Assumption2 pref U W 𝒞 𝒜 PC PA wC wA)
    (B D : Set S) (hB : B ∈ 𝒜) (hD : D ∈ 𝒜) :
    SourceTheory.Uniform.IsMoreInsensitive W 𝒜 𝒞 B D ↔
      ∃ φ : ℝ → ℝ, SourceTheory.Uniform.IsTransformation φ ∧ SourceTheory.Uniform.IsInsensitive φ (PA B) (PA D) ∧
        ∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p) := by sorry

end SourceTheory.InsensMatch
