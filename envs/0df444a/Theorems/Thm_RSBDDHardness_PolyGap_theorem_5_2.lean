-- Prove2me | Theorems.Thm_RSBDDHardness_PolyGap_theorem_5_2
-- name    : RSBDDHardness.PolyGap.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:27:04.730089+00:00
-- url     : https://prove2.me/theorems/1c063876-2ae8-4d99-8f1e-234f09632537
-- title:
--   Theorem 5.2 — elementary uniform positive moment completion
-- statement:
--   Fix real numbers $\rho>0$ and $C>2+2/\rho$. There is $D_0$ such that for every $d\ge D_0$, every prime $q$ with $q\ge d^{2+\rho}$, and $h=\lceil Cd\rceil$, every target $c=(c_1,\dots,c_d)\in\mathbb F_q^d$ is realized by an $h$-element subset $S\subseteq\mathbb F_q^\times$:
--   $$\sum_{a\in S}a^j=c_j,\qquad 1\le j\le d.$$
--
--   The cardinality $h$ is the same for every target, which is what the balanced completion (Theorem 7.1) needs.
--
--   Differences from the source:
--   - encoding: indexed targets c_1, …, c_d (or r_1, …, r_d) → a function on ℕ of which only the values at 1, …, d are used; reason: same instances; avoids Fin-indexed casts
--   - encoding: for all sufficiently large d → there exists D₀ such that the conclusion holds for all d ≥ D₀; reason: standard reading of the phrase
--   - encoding: S ⊆ F_q^× → S a finite set of ZMod q with 0 ∉ S; reason: same sets
-- source:
--   Daqing Wan, Jun Zhang, NP-Hardness of Bounded Distance Decoding for Reed–Solomon Codes, STOC 2027 submission #449 (October 2026), Theorem 5.2, PDF p. 16 (printed p. 15); PDF SHA-256 d60d9a54b73aa972494f130439dc6e07f8c7b33556741f8324d22cf45218e22b

import Mathlib
import Definitions.Def_RSBDDHardness_PolyGap_Algebra
set_option autoImplicit false
open scoped BigOperators
open Classical

namespace RSBDDHardness.PolyGap

/-- Theorem 5.2 (Elementary uniform positive moment completion), PDF 16. Fix `ρ > 0` and
`C > 2 + 2/ρ`. For all sufficiently large `d`, every prime `q ≥ d^{2+ρ}` and `h = ⌈Cd⌉`, every
`c ∈ 𝔽_q^d` has an `h`-element subset `S ⊆ 𝔽_q^×` with `∑_{a∈S} a^j = c_j`, `1 ≤ j ≤ d`. -/
theorem theorem_5_2 (ρ C : ℝ) (hρ : 0 < ρ) (hC : 2 + 2 / ρ < C) :
    ∃ D₀ : ℕ, ∀ d : ℕ, D₀ ≤ d → ∀ q : ℕ, q.Prime → (d : ℝ) ^ (2 + ρ) ≤ (q : ℝ) →
      ∀ c : ℕ → ZMod q, ∃ S : Finset (ZMod q),
        (0 : ZMod q) ∉ S ∧ S.card = ⌈C * (d : ℝ)⌉₊ ∧ RealizesMoments S d c := by sorry

end RSBDDHardness.PolyGap
