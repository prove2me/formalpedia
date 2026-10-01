-- Prove2me | Theorems.Thm_PhilipponMultiplicity_pointed_section_five_isolated_cosets
-- name    : PhilipponMultiplicity.pointed_section_five_isolated_cosets
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T11:40:34.227884+00:00
-- url     : https://prove2.me/theorems/9522f00d-d75f-453b-8300-4c36fdf42090
-- title:
--   Pointed Section 5 selection with isolated sampled cosets
-- statement:
--   Let $K$ be a Philippon base field, let $G$ be an embedded product of commutative algebraic groups with $n=\dim G>0$, and let $A$ be an analytic subgroup. Fix Section 5 input: a finite set $\Sigma$ containing $0$, a multihomogeneous nonzero polynomial $P$ of multidegree $D$, contact at least $nT+1$ on $\Sigma(n)$, and the bounded translation atlases. Write $I_r$ for the resulting polynomial-operator ideal chain.
--
--   There exist an integer $1\le r\le n$, a closed irreducible subset $V\subseteq G$ containing $0$, and a connected algebraic subgroup $H$ whose carrier is the identity component of the translation stabilizer of $V$, such that, with
--   $$
--   J=\sum_{v\in V}\tau_v I_r,
--   $$
--   every sampled coset $g+H$, $g\in\Sigma$, is incompletely defined both by $J$ and by its order-$T$ differential prolongation $\partial_A^{\le T}J$.
--
--   Incomplete definition has the original minimal-prime meaning: the coset is a union of isolated components, rather than merely a subset of the zero locus. This is the pointed geometric selection needed for Philippon's 1987 sampled-translates addendum. It does not assert that $V$ has globally maximal dimension in $Z(I_r)$.
--
--   **Formalization Note.** The chain and translated ideals are the previously published concrete definitions. The identity component is taken in the induced Zariski topology. No multiplicity lower bound, defining-degree bound, or Hilbert inequality is part of this statement. This is an Open geometric lemma; the parent reduction does not prove its existence assertion.
-- source:
--   Philippon, Errata et addenda (1987), p. 398, the first addendum (choice of V containing the identity), https://numdam.org/articles/10.24033/bsmf.2084/ ; combined with the isolated-coset step of the proof of Lemma 5.1 in Philippon (1986), pp. 381–382, https://numdam.org/articles/10.24033/bsmf.2060/ . This is an explicit geometric extraction of that refinement, not a verbatim separately numbered lemma.

import Definitions.Def_PhilipponMultiplicity_Support
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

/-- The pointed geometric selection required by the 1987 addendum.
This does not require the translating variety to have globally maximal dimension. -/
theorem pointed_section_five_isolated_cosets
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hn : 0 < G.dimension)
    (A : AnalyticSubgroup G) (C : SectionFiveInput G A) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ G.dimension ∧
      ∃ V : Set G.Point, 0 ∈ V ∧
        @IsClosed _ G.zariskiTopology V ∧ @IsIrreducible _ G.zariskiTopology V ∧
        ∃ H : AlgebraicSubgroup G,
          H.carrier = @connectedComponentIn _ G.zariskiTopology
            (setStabilizer G V : Set G.Point) 0 ∧ H.IsConnected ∧
          ∀ g ∈ C.samplingSet,
            IncompletelyDefines G
              (⨆ v : V, translatedIdeal G v.val (C.idealChain r))
              (translate g H.carrier) ∧
            IncompletelyDefines G
              (differentialIdeal A 0 C.contactParameter
                (⨆ v : V, translatedIdeal G v.val (C.idealChain r)))
              (translate g H.carrier) := by sorry

end PhilipponMultiplicity
