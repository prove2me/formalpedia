-- Prove2me | Theorems.Thm_SubsetSumPartialMatch_SubsetSum_structured_column_circuit
-- name    : SubsetSumPartialMatch.SubsetSum.structured_column_circuit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:24.208084+00:00
-- url     : https://prove2.me/theorems/ab8dc8f1-3a8b-4d21-a7df-e5ca8131e630
-- title:
--   Lemma 3.7 — structured-column colored circuit
-- statement:
--   Let $k$ be even and let $a,b>0$ be such that $ak$ and $bk$ are integers with $4ak\le k-bk$. Let $B\subseteq[k]$ with $|B|=bk$. Then the restriction of $P_{k,1/2}$ to the columns $\mathcal Y_B$ has a colored EXACT$_\mathbb Z$ circuit $C_B$ whose colors are ordered pairs $(\mu,\theta)$ with $a\le\mu\le2a$, $\mu\le\theta\le2\mu$ and $\mu k,\theta k\in\mathbb Z$. Moreover, for every color $(\mu,\theta)$ and every binary string $x$, writing $C'=(C_B)_{(\mu,\theta)}$,
--   $$\deg_L(C')\le O^*\bigl(2^{(h(1-b,\mu)-2\mu)k}\bigr),$$
--   $$\mathbb E_z\bigl[\deg_L(C',x\oplus z)\bigr]\le O^*\bigl(2^{(h(1-b,\mu)+h(2\mu,\theta)-4\mu)k}\bigr),$$
--   $$\deg_R(C')\le2^{(b-1/2+2a+h(a,\mu-a)+h(\mu,\theta-\mu))k},$$
--   where $z\in\{0,1\}^k$ is uniform subject to $z_i=0$ for all $i\in B$. Here $O^*$ hides only factors polynomial in $k$, uniformly in $B$ and the color.
--
--   This is the building block of the construction: it handles the queries whose specified bits outside $B$ are balanced.
--
--   Differences from the source:
--   - reading: $O^*$ hides factors polynomial in $k$, uniformly in $B$ and the color → one factor $(k+1)^c$ with $c$ absolute, chosen before $k,a,b,B$; reason: Theorem 3.8 applies the lemma at rounded parameters that change with $k$, so the polynomial cannot depend on $a,b$; the proof gives $k(2\mu k+1)$
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 23, Lemma 3.7

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Circuit
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Entropy

namespace SubsetSumPartialMatch.SubsetSum

/-- Lemma 3.7. Let `k` be even and `a, b > 0` with `ak, bk` integers and `4ak ≤ k - bk`, and let
`B ⊆ [k]` have `|B| = bk`. The restriction of `P_{k,1/2}` to the columns `Y_B` has a colored EXACT_Z
circuit whose colors are pairs `(µ, θ)` with `a ≤ µ ≤ 2a`, `µ ≤ θ ≤ 2µ`, `µk, θk ∈ ℤ`, and the three
degree bounds of the source hold for every color and every binary string. The factor `(k+1)^c` is
the source's `O*`: it is polynomial in `k` and uniform in `B`, the color, `a` and `b`. -/
theorem structured_column_circuit :
    ∃ c : ℕ, ∀ (k : ℕ) (a b : ℝ), Even k → 0 < a → 0 < b →
      (∃ u : ℕ, a * k = u) → (∃ v : ℕ, b * k = v) → 4 * a * k ≤ k - b * k →
      ∀ B : Finset (Fin k), (B.card : ℝ) = b * k →
        ∃ C : ColoredCircuit (BinStr k) (structuredCols k a B) (ℝ × ℝ),
          C.toLinCircuit.Computes (pmRestrict (structuredCols k a B)) ∧
          ∀ ζ ∈ C.colors, ζ ∈ colorDomain a ∧ (∃ u : ℕ, ζ.1 * k = u) ∧ (∃ v : ℕ, ζ.2 * k = v) ∧
            ((C.part ζ).degL : ℝ) ≤
              ((k : ℝ) + 1) ^ c * (2 : ℝ) ^ ((hgen (1 - b) ζ.1 - 2 * ζ.1) * k) ∧
            (∀ x : BinStr k, offAverage B (fun z => ((C.part ζ).degLAt (xorStr x z) : ℝ)) ≤
              ((k : ℝ) + 1) ^ c *
                (2 : ℝ) ^ ((hgen (1 - b) ζ.1 + hgen (2 * ζ.1) ζ.2 - 4 * ζ.1) * k)) ∧
            ((C.part ζ).degR : ℝ) ≤
              (2 : ℝ) ^ ((b - 1 / 2 + 2 * a + hgen a (ζ.1 - a) + hgen ζ.1 (ζ.2 - ζ.1)) * k) := by sorry

end SubsetSumPartialMatch.SubsetSum
