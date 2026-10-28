-- Prove2me | Theorems.Thm_SourceTheory_Uniform_qualitative_probability_representation
-- name    : SourceTheory.Uniform.qualitative_probability_representation
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T17:26:48.564598+00:00
-- url     : https://prove2.me/theorems/cbc7f302-cbc6-4d1c-9421-8df9c930e491
-- title:
--   Proof of Theorem 1, p. 8780 (via Krantz et al. 1971, Thm. 5.2.2) — an additive, convex-ranged, Archimedean event order has a unique representing probability
-- statement:
--   Let $\mathcal S$ be an algebra of subsets of a set $S$ and let $W$ be a real function on events with $W(\emptyset)=0$, $W(S)=1$, monotone on $\mathcal S$ ($B\subseteq A$ implies $W(B)\le W(A)$). Write $A\succcurlyeq A'$ for $W(A)\ge W(A')$. Assume:
--
--   1. **Additivity (de Finetti).** For $E,F,H\in\mathcal S$ with $E\cap H=F\cap H=\emptyset$,
--   $$W(F)\le W(E)\iff W(F\cup H)\le W(E\cup H).$$
--   2. **Convex rangedness (event solvability).** For $A\subseteq C$ in $\mathcal S$ and $W(A)\le\mu\le W(C)$ there is $B\in\mathcal S$ with $A\subseteq B\subseteq C$ and $W(B)=\mu$.
--   3. **Archimedean axiom.** There is no infinite sequence of pairwise disjoint events of $\mathcal S$ that all have the same positive weight.
--
--   Then there is a finitely additive probability measure $P$ on $\mathcal S$ that represents the event order,
--   $$W(A')\le W(A)\iff P(A')\le P(A)\qquad(A,A'\in\mathcal S),$$
--   and it is unique: every finitely additive probability measure $Q$ on $\mathcal S$ with the same representation property agrees with $P$ on $\mathcal S$.
--
--   This is the qualitative-probability representation step that Baillon et al. (2025) take from Krantz et al. (1971, Theorem 5.2.2) in the proof of Theorem 1, there applied to the event order $A\succcurlyeq C\iff W(A)\ge W(C)$ on a source. Their Lemma B.1 supplies additivity. Krantz et al.'s solvability axiom is replaced here by convex rangedness, which is what the paper uses ("their axiom 5 follows from event solvability"), and the Archimedean axiom is the one in the paper's Assumption 1, restricted to $\mathcal S$.
-- source:
--   Baillon, Bleichrodt, Li, Wakker (2025), Source Theory: A Tractable and Positive Ambiguity Theory, Management Science 71(10), App. B, proof of Theorem 1, p. 8780 (invoking Krantz, Luce, Suppes, Tversky (1971), Foundations of Measurement Vol. I, Theorem 5.2.2); Archimedean axiom from Assumption 1, p. 8771

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.Uniform

open Set MeasureTheory

/-- Representation step of the proof of Theorem 1 (Baillon et al. 2025, App. B, p. 8780), which
invokes Krantz et al. (1971, Theorem 5.2.2): a qualitative probability on a set algebra `𝒮`,
given by a monotone weighting `W` with `W ∅ = 0`, `W univ = 1` that is additive in de Finetti's
sense, convex ranged (event solvability) and Archimedean, is represented by a unique finitely
additive probability measure. -/
theorem qualitative_probability_representation {S : Type*} (𝒮 : Set (Set S)) (W : Set S → ℝ)
    (h𝒮 : IsSetAlgebra 𝒮) (hW0 : W ∅ = 0) (hW1 : W univ = 1)
    (hmono : ∀ A ∈ 𝒮, ∀ B ∈ 𝒮, B ⊆ A → W B ≤ W A)
    (hadd : ∀ E ∈ 𝒮, ∀ F ∈ 𝒮, ∀ H ∈ 𝒮, E ∩ H = ∅ → F ∩ H = ∅ →
      (W F ≤ W E ↔ W (F ∪ H) ≤ W (E ∪ H)))
    (hcr : IsConvexRanged 𝒮 W)
    (harch : ¬ ∃ E : ℕ → Set S, (∀ i, E i ∈ 𝒮) ∧ Pairwise (fun i j => Disjoint (E i) (E j)) ∧
      (∀ i, 0 < W (E i)) ∧ ∀ i j, W (E i) = W (E j)) :
    ∃ P : Set S → ℝ, IsProbOn 𝒮 P ∧ (∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, W A' ≤ W A ↔ P A' ≤ P A) ∧
      ∀ Q : Set S → ℝ, IsProbOn 𝒮 Q → (∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, W A' ≤ W A ↔ Q A' ≤ Q A) →
        ∀ E ∈ 𝒮, Q E = P E := by sorry

end SourceTheory.Uniform
