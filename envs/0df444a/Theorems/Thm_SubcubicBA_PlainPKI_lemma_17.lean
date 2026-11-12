-- Prove2me | Theorems.Thm_SubcubicBA_PlainPKI_lemma_17
-- name    : SubcubicBA.PlainPKI.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:44:10.305179+00:00
-- url     : https://prove2.me/theorems/8a1b6d26-9735-4026-b55c-d068c8a1749e
-- title:
--   Lemma 17 — MergeGroups preserves the invariant
-- statement:
--   Let $G_1,G_2$ be disjoint groups of parties with tuples $(h_1,H_1)$ and $(h_2,H_2)$ satisfying the invariant: $H_i\subseteq G_i$, $h_i$ is valid, every honest member of $H_i$ knows the value of $h_i$, and at least $(|G_i|-|H_i|)/2$ parties of $G_i\setminus H_i$ are byzantine. Let $K\subseteq H_2$ be the members of $H_2$ that broadcast $0$, and assume the two communication facts of p. 28:
--   1. if $H_1$ contains an honest party, then $K$ contains only byzantine parties;
--   2. if $H_1\ne\emptyset$, every honest member of $H_2\setminus K$ knows the value of $h_1$.
--
--   Then every tuple $(h,H)$ that MergeGroups may return (for every choice of $K'\subseteq K$ with $|K'|=|H_1|$, respectively $H_1'\subseteq H_1$ with $|H_1'|=|K|$) satisfies the invariant for $G_1\cup G_2$.
--
--   This is the dynamic-programming step of ValidatedAgreement, which keeps the dependence on the input length linear.
--
--   Differences from the source:
--   - generalization: MergeGroups inside ValidatedAgreement → an abstract set-level statement whose communication facts (p. 28, lines 893–895, and the broadcast results) are hypotheses; reason: the proof uses only these facts; the protocol's run is a special case
--   - encoding: "h is the accumulator of a valid input", "knows the value associated with h" → abstract predicates valid and knows; reason: the invariant does not depend on how accumulators are built
--   - encoding: "Let K′ be a subset of K of size |H₁|", "Let H₁′ be a subset of H₁ of size |K|" → every such choice; reason: the arbitrary choices quantified universally
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), Lemma 17, p. 28 (invariant p. 27, MergeGroups p. 28)

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Model
import Definitions.Def_SubcubicBA_PlainPKI_Proofs

namespace SubcubicBA.PlainPKI

/-- Lemma 17 (p. 28). -/
theorem lemma_17 {α : Type} (Bz : Finset ℕ) (valid : α → Prop) (knows : ℕ → α → Prop)
    (G₁ G₂ H₁ H₂ K : Finset ℕ) (h₁ h₂ : α) (out : α × Finset ℕ)
    (hdisj : Disjoint G₁ G₂)
    (hinv₁ : MergeInv Bz valid knows G₁ h₁ H₁) (hinv₂ : MergeInv Bz valid knows G₂ h₂ H₂)
    (hK : K ⊆ H₂)
    (hsend : (∃ p ∈ H₁, p ∉ Bz) → ∀ p ∈ K, p ∈ Bz)
    (hrecv : H₁ ≠ ∅ → ∀ p ∈ H₂ \ K, p ∉ Bz → knows p h₁)
    (hout : MergeResult h₁ h₂ H₁ H₂ K out) :
    MergeInv Bz valid knows (G₁ ∪ G₂) out.1 out.2 := by sorry

end SubcubicBA.PlainPKI
