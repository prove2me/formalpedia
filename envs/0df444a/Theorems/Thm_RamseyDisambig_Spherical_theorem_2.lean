-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_theorem_2
-- name    : RamseyDisambig.Spherical.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:30:51.618192+00:00
-- url     : https://prove2.me/theorems/e9bbb0cc-5433-40cd-b333-971c24a36d58
-- title:
--   Theorem 2 — Gap-Hamming Disambiguation
-- statement:
--   Fix $0<\varepsilon<1/2$ and a natural number $k$. There is a positive threshold dimension $N_0$ such that for every $N\ge N_0$ and every disambiguation $c$ of the Gap-Hamming matrix $H_\varepsilon^N$,
--   $$k\le\operatorname{VCdim}(c).$$
--   Here $H_\varepsilon^N$ has row and column set $\{0,1\}^N$, prescribed value $0$ at Hamming distance at most $\varepsilon N$, and prescribed value $1$ at distance at least $(1-\varepsilon)N$. Intermediate entries are arbitrary and completions need not be symmetric.
--
--   The threshold is uniform over every completion and covers all larger dimensions. This is the paper's discrete large-margin obstruction.
--
--   Differences from the source:
--   - reading: dimensions in ℕ under the positive-integer reading → a threshold N₀ ≥ 1 and all natural dimensions N ≥ N₀; reason: restricting the threshold to be positive does not change eventual truth
--   - generalization: k ∈ ℕ, read positively → all k : ℕ, including k = 0; reason: the additional case is automatic because VC-dimension is nonnegative
--   - encoding: Gap-Hamming binary disambiguation and its VC-dimension → Fin N → Bool, Option Bool partial entries, real Hamming thresholds and row-first ℕ∞ VC-dimension; reason: this preserves every completion and avoids rounding the real thresholds
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Theorem 2, p. 4 (restated and proved p. 13; printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Cube
import Definitions.Def_NatureSLT_GrowthFunction_vcDim

set_option autoImplicit false

namespace RamseyDisambig.Spherical

/-- Theorem 2, p. 4 (proof p. 13). Includes the trivial k = 0 case. -/
theorem theorem_2 (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) (k : ℕ) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ c : Cube N → Cube N → Bool, IsGapHammingDisambiguation ε N c →
        (k : ℕ∞) ≤ NatureSLT.GrowthFunction.vcDim c := by sorry

end RamseyDisambig.Spherical
