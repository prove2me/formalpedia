-- Prove2me | Theorems.Thm_SteinerAPX_lemma_8
-- name    : SteinerAPX.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:29.355801+00:00
-- url     : https://prove2.me/theorems/0fd09885-47b3-4cb7-a304-0f5f3ad2d598
-- title:
--   Lemma 8 (cable recovery) — adding $O(\rho L)$ to a tree on $P_\rho$ yields disjoint trees $T_i$ along the cables of total length $\ge L$
-- statement:
--   For every constant $A>0$ there is a constant $C>0$ with the following property. Let a well-formed, separated cable layout of a 3DM-3 instance in some $\mathbb R^D$ be given, with total cable length $L$, let $0<\rho\le1/100$, and let $T$ be a network spanning $P_\rho$ with $\operatorname{len}(T)\le A\,L$. Then there are a network $N_+$ with $\operatorname{len}(N_+)\le C\rho L$ and, for every label $i$, a tree of line segments $T_i$ such that
--
--   1. every point of $T_i$ lies on $T$ or on $N_+$;
--   2. $T_i$ contains the sampled terminals on $\Gamma_i$;
--   3. the $T_i$ are pairwise disjoint;
--   4. every point of $T_i$ is within distance $\rho$ of $\Gamma_i$;
--   5. $\sum_i\operatorname{len}(T_i)\ge L$.
--
--   Cable recovery reduces a tree on the sampled terminals to a configuration of the cable problem: recovered cables plus connectors between them.
--
--   Differences from the source:
--   - generalization: T a Steiner tree on Pρ → T any network with connected carrier containing Pρ; reason: the proof uses only that T is connected and contains Pρ; every tree spanning Pρ is such a network, so the statement specializes to the source's
--   - encoding: length O(L) and added length O(ρL) → for every A > 0 a constant C > 0, uniform over instances, layouts, dimensions and ρ, with len T ≤ A·L and len added ≤ C·ρ·L; reason: the standard reading of the O-notation with the hidden constant depending only on the constant in the hypothesis
--   - generalization: b₁, b₂ two orthogonal unit coordinate vectors of ℝᴰ → b₁, b₂ any orthonormal pair (CableLayout.WellFormed) in any EuclideanSpace ℝ ι; reason: a linear isometry of ℝᴰ maps any orthonormal pair onto two coordinate vectors and preserves every quantity in the statement, so the statement specializes to the source's coordinate vectors
--   - encoding: a 3DM-3 instance H with three parts of size r → an Inst3DM, whose parts have size r ≥ 1; reason: excludes only the empty instance (no elements, no triples, no gadgets), which the paper never considers (it assumes 4r ≤ m, §2)
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), Lemma 8, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_SteinerAPX_Separated
import Definitions.Def_SteinerAPX_samples

namespace SteinerAPX

open Inst3DM CableLayout

/-- **Lemma 8 (cable recovery).** S. Bartlmae, *Inapproximability of Euclidean Steiner Tree*,
STOC 2027 submission (manuscript sha256 6f78a9ea…), Lemma 8, p.16 (PDF p.18): "Let T be a Steiner
tree on Pρ of length O(L). By adding segments of total length O(ρL) to T, we obtain a network
containing pairwise disjoint trees Ti, one for each cable Γi. Each Ti spans the sampled terminals
on Γi and lies within distance ρ of that cable; together, these trees have total length at least
L."

For every `A > 0` there is `C > 0` such that, for every well-formed, separated layout of a 3DM-3
instance in any `ℝᴰ`, every `0 < ρ ≤ 1/100` and every connected network `T` containing `Pρ` with
`len T ≤ A · L`, there is a network `added` with `len added ≤ C ρ L` and, for every label `i`, a tree
of segments `Tᵢ` whose points lie on `T` or on `added`, containing the samples of `Γᵢ`, with every
point within distance `ρ` of `Γᵢ`, such that the `Tᵢ` are pairwise disjoint and
`∑ᵢ len Tᵢ ≥ L`.

**Formalization Note** "Length O(L)" and "O(ρL)" are read as: for each constant `A`, a constant
`C` depending only on `A`, uniform over all instances, layouts, dimensions and `ρ`. `T` is any
network with connected carrier containing `Pρ`; a Steiner tree is one. The `Tᵢ` need not consist of
whole segments of `T`: their points lie on `T ∪ added`. -/
theorem lemma_8 :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type} [Fintype ι] (H : Inst3DM) (L : CableLayout H (EuclideanSpace ℝ ι)),
      H.IsThreeDM3 → L.WellFormed → Separated L →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 100 →
      ∀ T : Network (EuclideanSpace ℝ ι), Spans (samples L ρ) T → len T ≤ A * L.totalLen →
      ∃ added : Network (EuclideanSpace ℝ ι), len added ≤ C * ρ * L.totalLen ∧
      ∃ Tr : Label H → Network (EuclideanSpace ℝ ι),
        (∀ i, IsTreeNet (Tr i)) ∧
        (∀ i, carrier (Tr i) ⊆ carrier T ∪ carrier added) ∧
        (∀ i, cableSamples L ρ i ⊆ carrier (Tr i)) ∧
        (∀ i j, i ≠ j → Disjoint (carrier (Tr i)) (carrier (Tr j))) ∧
        (∀ i, ∀ x ∈ carrier (Tr i), Metric.infDist x (carrier (L.cable i)) ≤ ρ) ∧
        L.totalLen ≤ ∑ i : Label H, len (Tr i) := by sorry

end SteinerAPX
