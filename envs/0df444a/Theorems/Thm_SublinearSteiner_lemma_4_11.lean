-- Prove2me | Theorems.Thm_SublinearSteiner_lemma_4_11
-- name    : SublinearSteiner.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:48:42.134217+00:00
-- url     : https://prove2.me/theorems/0bec3cfe-94ce-45bd-b84b-d9222c80472a
-- title:
--   Lemma 4.11 — mutual capping, (4.20)
-- statement:
--   Let $U$ be as in Lemma 4.8, let $b\ge1$, and take the port multigraph on $U$ with the capped lists $L(C)$. Every independent set $I\subseteq U$ of this multigraph satisfies
--   $$\Psi_U\le|U|-|I|+2n/b.$$
--   Consequently every maximal matching, and hence the expected random-greedy matching size $\mu$, satisfies
--   $$\Psi_U/2-n/b\le\mu\le\Psi_U.$$
--
--   Capping the incidence lists thus keeps the saving a matching problem, while bounding the degrees.
--
--   Differences from the source:
--   - generalization: b = ⌈100n/(εg₋)⌉ → any integer b ≥ 1; reason: the proof uses no other property of b, and the printed b is such an integer for n ≥ 1
--   - encoding: a fixed public order → any permutation of the points; reason: a fixed order is one such permutation
--   - generalization: N the retained cover at a scale of §4.6, in the floored metric, with D from the selected balls of Lemma 4.10 → any N ⊆ T, any scale a > 0, any metric, any set S of centers and any size bound B; reason: the proof uses only the eligibility of rows and the caps of the lists; the page's U is the case of its own N, S and B
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 4.11, (4.20), p.27

import Mathlib
import Definitions.Def_SublinearSteiner_PortGraph

open scoped Classical

namespace SublinearSteiner

/-- Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 4.11 (Mutual capping), (4.20), p.27. Every independent set `I ⊆ U` of this multigraph satisfies
`Ψ_U ≤ |U| − |I| + 2n/b`. Consequently every maximal matching, and hence the expected random-greedy matching size `μ`, satisfies
`Ψ_U/2 − n/b ≤ μ ≤ Ψ_U`.

**Formalization Note.** `U` is as in Lemma 4.8, and rows are indexed by all of `V`. The cap `b` is any integer `b ≥ 1`, which contains the page's
`⌈100n/(εg₋)⌉` whenever `n ≥ 1`: the proof uses no other property. The order `ord` is any public order. The maximal-matching clause is
stated for the size of `M`, and then the same bounds for `μ`. -/
theorem lemma_4_11 {n : ℕ} (w : FinMetric n) (T N S : Finset (Fin n)) (a : ℝ) (ha : 0 < a) (hN : N ⊆ T)
    (B b : ℕ) (hb : 1 ≤ b) (ord : Equiv.Perm (Fin n)) :
    (∀ I : Finset ↥(restComps w T N S a B),
      (portGraph w N a ord b (restComps w T N S a B)).IsIndependent I →
      (restrictedSaving w N a (restComps w T N S a B) : ℝ) ≤
        ((restComps w T N S a B).card : ℝ) - I.card + 2 * n / b) ∧
    (∀ M : Finset (PortCopy w N a ord b (restComps w T N S a B)),
      (portGraph w N a ord b (restComps w T N S a B)).IsMaximalMatching M →
      (restrictedSaving w N a (restComps w T N S a B) : ℝ) / 2 - n / b ≤ M.card ∧
        (M.card : ℝ) ≤ restrictedSaving w N a (restComps w T N S a B)) ∧
    (restrictedSaving w N a (restComps w T N S a B) : ℝ) / 2 - n / b ≤
        (portGraph w N a ord b (restComps w T N S a B)).expectedMatching ∧
      (portGraph w N a ord b (restComps w T N S a B)).expectedMatching ≤
        restrictedSaving w N a (restComps w T N S a B) := by sorry

end SublinearSteiner
