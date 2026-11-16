-- Prove2me | Theorems.Thm_RSBDDHardness_PolyGap_Supplement_theorem_a_2
-- name    : RSBDDHardness.PolyGap.Supplement.theorem_a_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:48:48.243528+00:00
-- url     : https://prove2.me/theorems/5ca02ace-ea24-419f-9810-f44ea10adaed
-- title:
--   Theorem A.2 — strong uniform positive moment completion
-- statement:
--   Fix real numbers $\rho>0$ and $C>1+2/\rho$. There exists a natural threshold $D_0$, depending only on $\rho,C$, such that for every natural $d\ge D_0$, every prime $q\ge d^{2+\rho}$, and every target $c=(c_1,\ldots,c_d)\in\mathbb F_q^d$, there is a subset $S\subseteq\mathbb F_q^\times$ with
--   $$
--   |S|=h=\lceil Cd\rceil,\qquad \sum_{a\in S}a^j=c_j\quad(1\le j\le d).
--   $$
--   The elements of $S$ are distinct and nonzero, and all prescribed moments hold simultaneously. This companion theorem sharpens the completion cardinality constant and is not used in the proof of the mission goal. Theorem A.1 supplies its supporting point-count estimates.
--
--   **Formalization Note** The constants $\rho,C$ range over all allowed real values. The single threshold precedes the prime and target quantifiers. Real powers express the field-size condition; the natural ceiling gives the exact subset cardinality, with positivity available by increasing the threshold. No hypothesis of $h<q$ or scalar completion is added.
--
--   Differences from the source:
--   - encoding: the prime field F_q and the target vector (c_1, …, c_d) → ZMod q with explicit q.Prime and c : ℕ → ZMod q, using only orders 1 through d; reason: these give exactly the same prime fields and prescribed targets; values outside 1 through d are ignored
--   - encoding: for all sufficiently large d, uniformly for every eligible q and c → ∃ D₀ : ℕ before ∀ d ≥ D₀, ∀ prime q ≥ d^(2+ρ), ∀ c; reason: the threshold depends only on ρ,C, exactly expressing the source uniformity
--   - encoding: an h-element subset S of F_q^×, where h = ⌈Cd⌉ → S : Finset (ZMod q), 0 ∉ S, S.card = ⌈C*(d:ℝ)⌉₊ and RealizesMoments S d c; reason: Finset enforces distinctness and RealizesMoments enforces every equation; for all sufficiently large positive d, C>1 makes the natural ceiling equal the ordinary ceiling
-- source:
--   Daqing Wan, Jun Zhang, NP-Hardness of Bounded Distance Decoding for Reed–Solomon Codes, STOC 2027 submission #449 (October 2026), Theorem A.2, PDF p. 31 (printed p. 30); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/449.pdf; SHA-256 d60d9a54b73aa972494f130439dc6e07f8c7b33556741f8324d22cf45218e22b

import Definitions.Def_RSBDDHardness_PolyGap_Algebra

set_option autoImplicit false

namespace RSBDDHardness.PolyGap.Supplement

/-- Wan–Zhang, STOC 2027 submission #449, Theorem A.2, PDF p.31 (printed p.30).
The threshold depends only on the arbitrary real constants ρ,C; it is uniform in q,c.
The cardinality is the exact ceiling, and the finite set consists of nonzero elements. -/
theorem theorem_a_2 (ρ C : ℝ) (hρ : 0 < ρ) (hC : 1 + 2 / ρ < C) :
    ∃ D₀ : ℕ, ∀ d : ℕ, D₀ ≤ d → ∀ q : ℕ, q.Prime →
      (d : ℝ) ^ (2 + ρ) ≤ (q : ℝ) → ∀ c : ℕ → ZMod q,
        ∃ S : Finset (ZMod q), (0 : ZMod q) ∉ S ∧
          S.card = ⌈C * (d : ℝ)⌉₊ ∧ RealizesMoments S d c := by sorry

end RSBDDHardness.PolyGap.Supplement
