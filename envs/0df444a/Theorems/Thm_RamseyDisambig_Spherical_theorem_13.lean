-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_theorem_13
-- name    : RamseyDisambig.Spherical.theorem_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:31:39.418081+00:00
-- url     : https://prove2.me/theorems/8d7aa7df-3c5a-4f50-91bc-cb5b435adbaf
-- title:
--   Theorem 13 — Gap colorings of a suitable torus have large VC-dimension
-- statement:
--   Let $0<\varepsilon<1/2$ and let $q\ge1$ be an integer. There exist a positive dimension $N$ and an even side length $R\ge2$ such that every $\varepsilon$-gap coloring $c:(\mathbb Z_R)^N\times(\mathbb Z_R)^N\to\{0,1\}$ satisfies
--   $$q\le\operatorname{VCdim}(c).$$
--   No distance-profile-canonical assumption is imposed on $c$. Both geometric parameters may depend on $\varepsilon,q$, but precede the coloring. This is the unconditional torus target used by Gap-Hamming disambiguation.
--
--   Differences from the source:
--   - reading: q ∈ ℕ and existential integer N and even integer R → q ≥ 1, N ≥ 1 and even R ≥ 2; reason: the positive-integer reading prevents zero-dimensional or zero-block witnesses from making the result vacuous; see paper.md, Recorded reading
--   - encoding: finite cyclic tori with the sum metric → positive side length in ZMod, shorter-arc real distances, and a finite real diameter supremum; reason: this represents the same finite metric space
--   - encoding: binary colorings and column VC-dimension → Bool labels with row-first NatureSLT.GrowthFunction.vcDim valued in ℕ∞; reason: these preserve all binary patterns and allow infinite VC-dimension
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Theorem 13, p. 12 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Torus
import Definitions.Def_NatureSLT_GrowthFunction_vcDim

set_option autoImplicit false

namespace RamseyDisambig.Spherical

/-- Theorem 13, p. 12. Positive dimensions and even side lengths at least two. -/
theorem theorem_13 (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) (q : ℕ) (hq : 1 ≤ q) :
    ∃ (N : ℕ) (R : ℕ+), 1 ≤ N ∧ 2 ≤ (R : ℕ) ∧ Even (R : ℕ) ∧
      ∀ c : Torus R N → Torus R N → Bool,
        GapColoring ε torusDistance c → (q : ℕ∞) ≤ NatureSLT.GrowthFunction.vcDim c := by sorry

end RamseyDisambig.Spherical
