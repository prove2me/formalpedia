-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_Supplement_lemma_5_5
-- name    : SubadditiveMMS580.Amplification.Supplement.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:01:20.696523+00:00
-- url     : https://prove2.me/theorems/c6595690-352a-4da5-a4db-362c6314503b
-- title:
--   Lemma 5.5 — exponential comparison bounds (25) and (26) on $R_V$
-- statement:
--   Let $Z$ and $Z_j$ be independent mean-one exponential random variables, and for coefficients $b_j$ let $V=\max_j b_jZ_j$ (empty maximum zero) and $R_V(x)=\mathbb E(xZ-V)^+$.
--
--   1. For every finite family of nonnegative coefficients $(b_j)_j$ and every $x\ge0$,
--   $$R_V(x)\ge\frac34x-\frac14\sum_jb_j,\qquad R_V(x)\ge\frac{73}{80}x-\frac12\sum_jb_j.\tag{25}$$
--   2. Let finitely many competitors $j$ have nonnegative coefficients $c_j(g)$ on the goods $g\in M$, put $b_g=\sum_jc_j(g)$ and $V_g=\max_jc_j(g)Z_j$, and let $\tilde v\ge0$ be auxiliary coefficients with $\tilde v(M)=1$. If $L=\sum_{g\in\operatorname{supp}(\tilde v)}b_g\le1$, then
--   $$\sum_{g\in M}R_{V_g}(\tilde v(g))\ge\frac{1}{1+L}.\tag{26}$$
--
--   These estimates verify the hypothesis (18) of the reservation theorem for the choices of §5.4 in the proof of Theorem 1.3.
--
--   Differences from the source:
--   - encoding: a finite family (b_j)_j; the other agents j ≠ i in (26) → families indexed by an arbitrary finite type ι; reason: the other agents form a finite index set; the bounds do not depend on the indexing
--   - encoding: supp(ṽ) → the goods g with ṽ(g) ≠ 0; reason: definition of the support
-- source:
--   Bo Li, Ankang Sun, Toward Constant-Factor Maximin Share Guarantees for Subadditive Valuations, STOC 2027 submission #580 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/580.pdf, sha256 7de124b5706e9e49301a281a1eb418a8ae32d04bf4cf0941b969cc3cde85e485, Lemma 5.5, p. 35 (PDF p. 35)

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Supplement_Reservation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation

open MultiAllocToAlloc.Subadditive MeasureTheory

namespace SubadditiveMMS580.Amplification.Supplement

/-- Lemma 5.5 (Li–Sun, STOC 2027 submission #580, p. 35): (25) for every finite family of
nonnegative coefficients `(b_j)_j`, `V = max_j b_j Z_j` and `x ≥ 0`,
`R_V(x) ≥ (3/4) x − (1/4) ∑_j b_j` and `R_V(x) ≥ (73/80) x − (1/2) ∑_j b_j`; (26) for competitors `j`
with nonnegative coefficients `c_j(g)`, `b_g = ∑_j c_j(g)`, `V_g = max_j c_j(g) Z_j`, and a
nonnegative `ṽ` with `ṽ(M) = 1`: if `L = ∑_{g ∈ supp ṽ} b_g ≤ 1` then
`∑_{g ∈ M} R_{V_g}(ṽ(g)) ≥ 1/(1 + L)`. -/
theorem lemma_5_5 :
    (∀ {ι : Type} [Fintype ι] (b : ι → ℝ), (∀ j, 0 ≤ b j) → ∀ x : ℝ, 0 ≤ x →
      3 / 4 * x - 1 / 4 * ∑ j, b j ≤ expComparison b x ∧
      73 / 80 * x - 1 / 2 * ∑ j, b j ≤ expComparison b x) ∧
    (∀ {m : ℕ} {ι : Type} [Fintype ι] (c : ι → Fin m → ℝ), (∀ j g, 0 ≤ c j g) →
      ∀ vt : Fin m → ℝ, (∀ g, 0 ≤ vt g) → ∑ g, vt g = 1 →
      ∑ g ∈ Finset.univ.filter (fun g => vt g ≠ 0), ∑ j, c j g ≤ 1 →
      1 / (1 + ∑ g ∈ Finset.univ.filter (fun g => vt g ≠ 0), ∑ j, c j g) ≤
        ∑ g, expComparison (fun j => c j g) (vt g)) := by sorry

end SubadditiveMMS580.Amplification.Supplement
