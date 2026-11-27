-- Prove2me | Theorems.Thm_SubmodMFG_Supplement_lemma_A_3
-- name    : SubmodMFG.Supplement.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:23:49.812921+00:00
-- url     : https://prove2.me/theorems/42f8c511-da86-5121-a5c6-4eb70a35a726
-- title:
--   Lemma A.3 — a Dedekind σ-complete lattice with a strictly increasing real map is Dedekind super complete
-- statement:
--   Let $L$ be a lattice that is **Dedekind σ-complete**: every nonempty countable subset bounded above (below) has a least upper bound (greatest lower bound). Suppose there is a **strictly increasing** map $F:L\to\mathbb R$, i.e.
--
--   1. $F(x)\le F(y)$ whenever $x\le y$, and
--   2. $x\le y$ and $F(x)=F(y)$ imply $x=y$.
--
--   Then $L$ is **Dedekind super complete**: every nonempty $S\subseteq L$ bounded above has a least upper bound $b$ and a countable $C\subseteq S$ with $\sup C=b$, and dually for sets bounded below.
--
--   The lemma reduces Dedekind super completeness of the lattice of constrained flows in Theorem 3.3 to countable completeness plus a strictly monotone functional.
--
--   **Formalization Note** The existence of the least upper bound, presupposed by "the same least upper bound" in Definition A.1, is part of the conclusion.
--
--   Differences from the source:
--   - encoding: Dedekind super complete: every nonempty subset bounded above (below) has a countable subset with the same least upper bound (greatest lower bound) → DedekindSuperCompleteOrd: a least upper bound b exists and some countable C ⊆ S has least upper bound b (dually); reason: the printed definition presupposes the bound; the paper uses it only for lattices in which it exists
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, Appendix A, Lemma A.3 and Definition A.2, p.33

import Mathlib
import Definitions.Def_SubmodMFG_Supplement_DedekindOrder

namespace SubmodMFG.Supplement

/-- **Lemma A.3** — a Dedekind σ-complete lattice with a strictly increasing real map is Dedekind
super complete.
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, Appendix A, Lemma A.3, p.33: "Let L be a Dedekind σ-complete lattice. If
there exists a strictly increasing map F : L → R, then L is Dedekind super complete."
Definition A.2, p.33: "F : L → R is strictly increasing if (i) F(x) ≤ F(y) for all x, y ∈ L with
x ≤ y, (ii) for all x, y ∈ L with x ≤ y and F(x) = F(y), it follows that x = y."

**Formalization Note.** `L` is a Mathlib `Lattice` (a partial order with binary suprema and
infima, as on p.33); conditions (i) and (ii) of Definition A.2 are the hypotheses `hF₁`, `hF₂`. -/
theorem lemma_A_3 {L : Type*} [Lattice L] (hL : DedekindSigmaComplete L) (F : L → ℝ)
    (hF₁ : ∀ x y : L, x ≤ y → F x ≤ F y) (hF₂ : ∀ x y : L, x ≤ y → F x = F y → x = y) :
    DedekindSuperCompleteOrd L := by sorry

end SubmodMFG.Supplement
