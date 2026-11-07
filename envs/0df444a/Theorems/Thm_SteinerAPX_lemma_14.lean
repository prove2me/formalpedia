-- Prove2me | Theorems.Thm_SteinerAPX_lemma_14
-- name    : SteinerAPX.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:36:48.164164+00:00
-- url     : https://prove2.me/theorems/129e5647-7a07-410b-abd4-9c7b4c40272b
-- title:
--   Lemma 14 (cleaning) — every tree on $P_\rho$ of length $\le\frac73L$ yields a clean network of length $\le\operatorname{len}(T)+C_2\rho L$
-- statement:
--   There is an absolute constant $C_2$ such that the following holds. Let a well-formed, separated cable layout of a 3DM-3 instance $H$ in some $\mathbb R^D$ be given, with total cable length $L$, let $0<\rho\le1/100$, and let $T$ be a network spanning $P_\rho$ with
--   $$
--   \operatorname{len}(T)\le\tfrac73 L .
--   $$
--   Then there is a matching $M$ of $H$ whose clean network has length at most $\operatorname{len}(T)+C_2\rho L$.
--
--   Cleaning gives the lower bound of the cable reduction: the triples of the good square connectors form a matching.
--
--   Differences from the source:
--   - generalization: T a tree on Pρ → T any network with connected carrier containing Pρ; reason: the proof uses only that T is connected and contains Pρ; every tree spanning Pρ is such a network, so the statement specializes to the source's
--   - generalization: b₁, b₂ two orthogonal unit coordinate vectors of ℝᴰ → b₁, b₂ any orthonormal pair (CableLayout.WellFormed) in any EuclideanSpace ℝ ι; reason: a linear isometry of ℝᴰ maps any orthonormal pair onto two coordinate vectors and preserves every quantity in the statement, so the statement specializes to the source's coordinate vectors
--   - encoding: a 3DM-3 instance H with three parts of size r → an Inst3DM, whose parts have size r ≥ 1; reason: excludes only the empty instance (no elements, no triples, no gadgets), which the paper never considers (it assumes 4r ≤ m, §2)
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), Lemma 14, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_SteinerAPX_Separated
import Definitions.Def_SteinerAPX_samples
import Definitions.Def_SteinerAPX_cleanNetwork

namespace SteinerAPX

open Inst3DM CableLayout

/-- **Lemma 14 (cleaning).** S. Bartlmae, *Inapproximability of Euclidean Steiner Tree*, STOC
2027 submission (manuscript sha256 6f78a9ea…), Lemma 14, p.19 (PDF p.21): "For every tree T on Pρ
with len(T) ≤ (7/3)L, there is a clean network of length at most len(T) + C2ρL, where C2 is an
absolute constant."

There is a constant `C₂` such that for every well-formed, separated layout of a 3DM-3 instance in
any `ℝᴰ`, every `0 < ρ ≤ 1/100`, and every connected network `T` containing `Pρ` with
`len T ≤ (7/3)L`, some matching `M` has a clean network of length at most `len T + C₂ ρ L`.

**Formalization Note** A clean network is `cleanNetwork L M` for a matching `M` (Definition 10).
`C₂` is chosen before the dimension, the instance, the layout and `ρ`. `T` is any network with
connected carrier containing `Pρ`; a tree is one. -/
theorem lemma_14 :
    ∃ C₂ : ℝ, ∀ {ι : Type} [Fintype ι] (H : Inst3DM) (L : CableLayout H (EuclideanSpace ℝ ι)),
      H.IsThreeDM3 → L.WellFormed → Separated L →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 100 →
      ∀ T : Network (EuclideanSpace ℝ ι), Spans (samples L ρ) T → len T ≤ 7 / 3 * L.totalLen →
      ∃ M : Finset (Fin H.r × Fin H.r × Fin H.r), H.IsMatching M ∧
        len (cleanNetwork L M) ≤ len T + C₂ * ρ * L.totalLen := by sorry

end SteinerAPX
