-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_lemma_12
-- name    : RamseyDisambig.Spherical.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:31:30.155859+00:00
-- url     : https://prove2.me/theorems/ff21ad1b-2799-4751-80fc-f1e5aecbf185
-- title:
--   Lemma 12 — Canonicalization on a torus
-- statement:
--   Let $0<\varepsilon<1/2$ and let $R,n\ge1$ be integers. There exists an integer $N\ge1$ such that every $\varepsilon$-gap coloring $c:(\mathbb Z_R)^N\times(\mathbb Z_R)^N\to\{0,1\}$ admits two maps $\iota_1,\iota_2:(\mathbb Z_R)^n\to(\mathbb Z_R)^N$ for which
--   $$\widehat c(x,y)=c(\iota_1(x),\iota_2(y))$$
--   is simultaneously an $\varepsilon/2$-gap coloring and distance-profile-canonical.
--
--   The dimension $N$ precedes the choice of coloring. The conclusion asks for arbitrary maps, and does not add injectivity or a block-map restriction. This is the structural target that applies to every gap coloring on the larger torus. For $R=1$ there is no gap coloring, as in the source's metric definition.
--
--   Differences from the source:
--   - reading: R,n,N ∈ ℕ → R,n,N ≥ 1; reason: the positive-integer reading prevents zero-dimensional or zero-block witnesses from making the result vacuous; see paper.md, Recorded reading
--   - encoding: cyclic tori and factorization through coordinatewise distances → ZMod with positive side length, real-valued distance profiles, and equality-of-profiles canonicality; reason: residue representatives and integer-valued real distances give exactly the source metric and canonicality
--   - encoding: binary coloring and pullback ĉ → Bool labels and the explicit two-map pullback; reason: labels and the conjunction of both conclusions are unchanged
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Lemma 12, p. 11 (proof pp. 11–12; printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Torus

set_option autoImplicit false

namespace RamseyDisambig.Spherical

/-- Lemma 12, p. 11. All torus dimensions and side lengths are positive. -/
theorem lemma_12 (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (R : ℕ+) (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ c : Torus R N → Torus R N → Bool,
      GapColoring ε torusDistance c →
      ∃ ι₁ ι₂ : Torus R n → Torus R N,
        GapColoring (ε / 2) torusDistance (fun x y => c (ι₁ x) (ι₂ y)) ∧
        DistanceProfileCanonical (fun x y => c (ι₁ x) (ι₂ y)) := by sorry

end RamseyDisambig.Spherical
