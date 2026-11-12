-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_lemma_8
-- name    : RamseyDisambig.Spherical.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T09:31:40.297256+00:00
-- url     : https://prove2.me/theorems/be286d17-059a-414b-9f4d-cf7ca5ba0f4a
-- title:
--   Lemma 8 — Shattering from distance profiles
-- statement:
--   Let $0<\varepsilon<1/2$ and let $q\ge1$ be an integer. There exist a positive dimension $n$ and an even side length $R\ge2$ such that every $\varepsilon$-gap, distance-profile-canonical coloring $c:(\mathbb Z_R)^n\times(\mathbb Z_R)^n\to\{0,1\}$ satisfies
--   $$q\le\operatorname{VCdim}(c).$$
--   Rows witness all binary patterns on the shattered columns. Neither $n$ nor $R$ depends on the coloring. This supplies the structured shattering target for the torus result.
--
--   Differences from the source:
--   - reading: q ∈ ℕ and existential integer n and even integer R → q ≥ 1, n ≥ 1 and even R ≥ 2; reason: the positive-integer reading prevents zero-dimensional or zero-block witnesses from making the result vacuous; see paper.md, Recorded reading
--   - encoding: cyclic tori and factorization through coordinatewise distances → ZMod with positive side length, real-valued distance profiles, and equality-of-profiles canonicality; reason: residue representatives and integer-valued real distances give exactly the source metric and canonicality
--   - encoding: binary colorings and column VC-dimension → Bool labels with row-first NatureSLT.GrowthFunction.vcDim valued in ℕ∞; reason: these preserve all binary patterns and allow infinite VC-dimension
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Lemma 8, p. 9 (proof pp. 9–10; printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Torus
import Definitions.Def_NatureSLT_GrowthFunction_vcDim

set_option autoImplicit false

namespace RamseyDisambig.Spherical

/-- Lemma 8, p. 9. Dimensions and even side lengths use the positive-integer reading. -/
theorem lemma_8 (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) (q : ℕ) (hq : 1 ≤ q) :
    ∃ (n : ℕ) (R : ℕ+), 1 ≤ n ∧ 2 ≤ (R : ℕ) ∧ Even (R : ℕ) ∧
      ∀ c : Torus R n → Torus R n → Bool,
        GapColoring ε torusDistance c → DistanceProfileCanonical c →
          (q : ℕ∞) ≤ NatureSLT.GrowthFunction.vcDim c := by sorry

end RamseyDisambig.Spherical
