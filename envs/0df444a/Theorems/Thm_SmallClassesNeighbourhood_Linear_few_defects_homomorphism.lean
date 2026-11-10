-- Prove2me | Theorems.Thm_SmallClassesNeighbourhood_Linear_few_defects_homomorphism
-- name    : SmallClassesNeighbourhood.Linear.few_defects_homomorphism
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:37:37.72764+00:00
-- url     : https://prove2.me/theorems/9b4fd0b9-9c22-42b2-b1a6-fdd560112802
-- title:
--   Claim 22 — profile–defect tree map and trivial stabiliser
-- statement:
--   Use all the few-defects selections with C_0 sufficiently large. The tagged induced profile–defect graph on P_0,D_0 has minimum degree at least Δ=⌈C^(1/3)⌉ and a spanning tree T of maximum degree at most Δ. Let B_0, v(P), u(D), B_0^pro,B_0^def,B_0^tree,A_0^pro,A_0^def,Q_0,R_0 and A′,B″ be the sets defined in the selection model, including both distinguishing directions and the witness's dual diversity. Let H_0⊆Aut(F[A′,B″]) preserve each of the seven named sets. The assignments
--
--   $$\phi(\sigma)(P)=P_{\sigma(v(P))},\qquad \phi(\sigma)(D)=D_{\sigma(u(D))}$$
--
--   land in Aut(T)_{D_0,P_0} and satisfy the identity and multiplication laws. Moreover,
--
--   $$(H_0)_{(B_0^{pro}\cup B_0^{def})}=\{1\}.$$
--
--   The three B-sets may overlap, as may A_0^pro and Q_0. Neither equivariance nor injectivity of the assignment is assumed. This is the final group comparison needed for the few-defects core.
--
--   Differences from the source:
--   - encoding: finite graphs and named vertex subsets → finite ambient carriers with cores on the subtype A ∪ B; reason: isolated padding is ignored; restriction to the union recovers exactly the source graph, including every uncoloured automorphism
--   - encoding: sufficiently large integer parameters → one existential positive natural threshold before every parameter and graph; reason: this is the uniform eventual meaning of sufficiently large, with no instance-dependent threshold
--   - encoding: the fixed choices in Section 3.2.1 → CanonicalData with the minimal pair, maximal separated R, representatives and good vertices; reason: these are precisely the preceding source selections; profiles, defects and representative images are computed from them
--   - encoding: φ on H_0 with values in the named automorphism stabilizer → the computed raw assignment lifts to automorphisms, preserving the named sets, with identity and multiplication laws on H_0; reason: the extension of φ outside H_0 is arbitrary and has no mathematical assertion; its restriction is exactly the source map, and landing is proved rather than assumed
--   - encoding: disjoint copies of the profile and defect families → a sum type and its actual selected vertex subtype; reason: identical subsets on opposite sides remain different vertices; the automorphism image preserves tags, hence both named parts
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), Claim 22 (context §3.2.3, printed pp. 19–22 / PDF pp. 20–23), printed p. 21 (PDF p. 22)

import Definitions.Def_SmallClassesNeighbourhood_Linear_fewDefects

namespace SmallClassesNeighbourhood.Linear

theorem few_defects_homomorphism :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ C0 : ℕ, L ≤ C0 →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : SimpleGraph V) (s : CanonicalData C0 F) (f : FewChoices s),
    (∃ φ : CoreAut F f.Aprime f.Bcore → (f.T ≃g f.T),
      (∀ σ, f.InH0 σ →
        (∀ x : PDVertex f.P0 f.D0, (φ σ x).val = f.assignment σ x) ∧
        (∀ x : PDVertex f.P0 f.D0,
          (∃ P : Finset V, (φ σ x).val = Sum.inl P) ↔
          (∃ P : Finset V, x.val = Sum.inl P))) ∧
      φ 1 = 1 ∧ ∀ σ τ, f.InH0 σ → f.InH0 τ → φ (σ * τ) = φ σ * φ τ) ∧
    (∀ σ : CoreAut F f.Aprime f.Bcore, f.InH0 σ →
      Fixes (ambientPerm σ) (f.Bpro ∪ f.Bdef) → σ = 1) := by sorry

end SmallClassesNeighbourhood.Linear
