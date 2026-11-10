-- Prove2me | Theorems.Thm_SmallClassesNeighbourhood_Linear_representative_defect_invariance
-- name    : SmallClassesNeighbourhood.Linear.representative_defect_invariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:36:43.424166+00:00
-- url     : https://prove2.me/theorems/4470c205-e849-4883-9f67-ab33ee856cd0
-- title:
--   Lemma 19 — representative and defect invariance
-- statement:
--   Fix the canonical setting with C_0 sufficiently large. Let A_0⊆A∖Q and B_0⊆B_good, put Q_0=rep(A_0), and choose a witness R_0⊆R, so Q_0 is R_0-diverse. Let σ be an automorphism of F[A_0∪Q_0,B_0∪R_0] preserving the four sets individually. Then
--
--   $$\sigma(rep(u))=rep(\sigma(u))\quad(u\in A_0),\qquad u\in D_v\iff\sigma(u)\in D_{\sigma(v)}\quad(u\in A_0,v\in B_0).$$
--
--   Both conclusions hold, including when A_0 or B_0 is empty. They provide the invariances needed in the two homomorphism claims.
--
--   Differences from the source:
--   - encoding: finite graphs and named vertex subsets → finite ambient carriers with cores on the subtype A ∪ B; reason: isolated padding is ignored; restriction to the union recovers exactly the source graph, including every uncoloured automorphism
--   - encoding: sufficiently large integer parameters → one existential positive natural threshold before every parameter and graph; reason: this is the uniform eventual meaning of sufficiently large, with no instance-dependent threshold
--   - encoding: the fixed choices in Section 3.2.1 → CanonicalData with the minimal pair, maximal separated R, representatives and good vertices; reason: these are precisely the preceding source selections; profiles, defects and representative images are computed from them
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), Lemma 19, printed p. 16 (PDF p. 17)

import Definitions.Def_SmallClassesNeighbourhood_Linear_canonical

namespace SmallClassesNeighbourhood.Linear

theorem representative_defect_invariance :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ C0 : ℕ, L ≤ C0 →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : SimpleGraph V) (s : CanonicalData C0 F)
    (A0 B0 R0 : Finset V) (hA : A0 ⊆ s.A \ s.Q) (hB : B0 ⊆ s.Bgood)
    (hR : s.Witness A0 R0)
    (σ : CoreAut F (A0 ∪ s.representativesOf A0) (B0 ∪ R0))
    (hσA : Preserves (ambientPerm σ) A0) (hσB : Preserves (ambientPerm σ) B0)
    (hσQ : Preserves (ambientPerm σ) (s.representativesOf A0))
    (hσR : Preserves (ambientPerm σ) R0),
    (∀ u ∈ A0, ambientPerm σ (s.representative u) = s.representative (ambientPerm σ u)) ∧
    (∀ u ∈ A0, ∀ v ∈ B0, u ∈ s.D v ↔ ambientPerm σ u ∈ s.D (ambientPerm σ v)) := by sorry

end SmallClassesNeighbourhood.Linear
