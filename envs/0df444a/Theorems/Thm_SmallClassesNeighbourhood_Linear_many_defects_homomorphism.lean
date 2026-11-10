-- Prove2me | Theorems.Thm_SmallClassesNeighbourhood_Linear_many_defects_homomorphism
-- name    : SmallClassesNeighbourhood.Linear.many_defects_homomorphism
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:37:47.784191+00:00
-- url     : https://prove2.me/theorems/cda2c7ce-4828-490d-8f27-d2f05074f0e3
-- title:
--   Claim 21 — defect restriction and the larger trivial stabiliser
-- statement:
--   Use the canonical setting and the many-defects selections, with C_0 sufficiently large: d≥C_0^2|A|; nonempty A_0⊆A∖Q and B_0⊆B_good minimally diverse in the defect graph with |B_0|=C_0^2|A_0|; B_0′ as in Lemma 14; Q_0=rep(A_0); and the small Q_0-diverse witness R_0. Put A′=A_0∪Q_0 and B″=B_0′∪R_0. Let H=Aut(F[A′,B″]) and H_0 preserve A_0,Q_0,R_0,B_0′ setwise. Restriction to A_0∪B_0′ lands in the defect-graph automorphisms preserving both parts and satisfies
--
--   $$\phi(1)=1,\qquad \phi(\sigma\tau)=\phi(\sigma)\phi(\tau)\quad(\sigma,\tau\in H_0),\qquad (H_{Q_0})_{(A_0\cup B_0')}=\{1\}.$$
--
--   The final assertion concerns the larger subgroup of H preserving Q_0 and fixing A_0∪B_0′ pointwise, not merely the kernel within H_0. No landing or homomorphism condition is a hypothesis. This is the many-defects group comparison.
--
--   Differences from the source:
--   - encoding: finite graphs and named vertex subsets → finite ambient carriers with cores on the subtype A ∪ B; reason: isolated padding is ignored; restriction to the union recovers exactly the source graph, including every uncoloured automorphism
--   - encoding: sufficiently large integer parameters → one existential positive natural threshold before every parameter and graph; reason: this is the uniform eventual meaning of sufficiently large, with no instance-dependent threshold
--   - encoding: the fixed choices in Section 3.2.1 → CanonicalData with the minimal pair, maximal separated R, representatives and good vertices; reason: these are precisely the preceding source selections; profiles, defects and representative images are computed from them
--   - encoding: φ on H_0 with values in the named automorphism stabilizer → the computed raw assignment lifts to automorphisms, preserving the named sets, with identity and multiplication laws on H_0; reason: the extension of φ outside H_0 is arbitrary and has no mathematical assertion; its restriction is exactly the source map, and landing is proved rather than assumed
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), Claim 21 (context §3.2.2, printed pp. 17–19 / PDF pp. 18–20), printed p. 18 (PDF p. 19)

import Definitions.Def_SmallClassesNeighbourhood_Linear_manyDefects

namespace SmallClassesNeighbourhood.Linear

theorem many_defects_homomorphism :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ C0 : ℕ, L ≤ C0 →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : SimpleGraph V) (s : CanonicalData C0 F) (m : ManyChoices s),
    (∃ φ : CoreAut F m.Aprime m.Bcore → CoreAut s.defectGraph m.A0 m.Bsmall,
      (∀ σ, m.InH0 σ →
        Preserves (ambientPerm (φ σ)) m.A0 ∧ Preserves (ambientPerm (φ σ)) m.Bsmall ∧
        ∀ x : {v : V // v ∈ m.A0 ∪ m.Bsmall}, (φ σ x).val = m.assignment σ x) ∧
      φ 1 = 1 ∧ ∀ σ τ, m.InH0 σ → m.InH0 τ → φ (σ * τ) = φ σ * φ τ) ∧
    (∀ σ : CoreAut F m.Aprime m.Bcore,
      Preserves (ambientPerm σ) m.Q0 → Fixes (ambientPerm σ) (m.A0 ∪ m.Bsmall) → σ = 1) := by sorry

end SmallClassesNeighbourhood.Linear
