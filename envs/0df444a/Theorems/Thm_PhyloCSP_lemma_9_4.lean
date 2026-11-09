-- Prove2me | Theorems.Thm_PhyloCSP_lemma_9_4
-- name    : PhyloCSP.lemma_9_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:24:03.323252+00:00
-- url     : https://prove2.me/theorems/79b70a3d-4445-4fe3-91b0-5e32081f6912
-- title:
--   Lemma 9.4 — the rank limits exist and realize $\sim$ and $\prec$
-- statement:
--   In the setting of Lemma 9.2, let $z_1,z_2,\dots$ be an enumeration of $Z$ and define
--   $$
--   r(x)=\lim_{n\to\infty}\frac{\lvert\{i\in[n]:z_i\prec x\}\rvert}{n}+\frac12\lim_{n\to\infty}\frac{\lvert\{i\in[n]:z_i\sim x\}\rvert}{n}. \tag{11}
--   $$
--   Then with probability one both limits exist for every leaf $x$, and for every pair of leaves
--   $$
--   r(x)=r(y)\iff x\sim y,\qquad r(x)<r(y)\iff x\prec y .
--   $$
--
--   The ranks $r(x)$ become the real-valued colors from which the template locations are recovered.
--
--   Differences from the source:
--   - encoding: an enumeration z₁, z₂, … of Z and [n] = {1, …, n} → an arbitrary bijection e : ℕ ≃ Z, z_i = e(i − 1), counts over {0, …, n − 1}; reason: 0-based indexing; the statement is made for every enumeration
--   - encoding: random linear order with invariant law → as in Lemma 9.2 (measurable, every realization a strict total order); reason: same setting
--   - encoding: the Fraïssé limit F = (Z, C) and its automorphism group Aut(F) → the concrete structure (Z, fraisseRel) of Definition 7.5, Z = Finset ℚ, and AutF its automorphism group; reason: Theorem 7.4 and Appendix B.1 identify the concrete structure with F, which is unique up to isomorphism; the statement is invariant under isomorphism
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Lemma 9.4 and eq. (11), p.28 (PDF p.30)

import Mathlib
import Definitions.Def_PhyloCSP_AutF
import Definitions.Def_PhyloCSP_RankRelations

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace PhyloCSP

open Classical in
/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027
submission (manuscript sha256 3444b6c0…682dac), Lemma 9.4, p.28 (PDF p.30), with (11): "We define
r(x) = lim_{n→∞} |{i ∈ [n] : zi ≺ x}|/n + 1/2 lim_{n→∞} |{i ∈ [n] : zi ∼ x}|/n. (11) … Lemma 9.4.
With probability one, the limits in (11) exist for every leaf x. Further, for every pair of leaves,
r(x) = r(y) if and only if x ∼ y, and r(x) < r(y) if and only if x ≺ y." Setting of Section 9.1:
a random linear order on `Z` with `Aut(F)`-invariant law; `z₁, z₂, …` an enumeration of `Z`.

**Formalization Note.** Same setting as Lemma 9.2. The enumeration is an arbitrary bijection
`e : ℕ ≃ Z` (`zᵢ = e (i - 1)`, so `[n]` becomes `{0, …, n-1}`); the statement holds for every `e`.
The two limits are `A x` and `B x`, and `r(x) = A x + B x / 2`. -/
theorem lemma_9_4 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (lt : Ω → Z → Z → Bool) (hmeas : Measurable lt)
    (horder : ∀ ω, IsStrictTotalOrder Z (fun a b => lt ω a b = true))
    (hinv : ∀ g ∈ AutF, P.map (fun ω a b => lt ω (g a) (g b)) = P.map lt) (e : ℕ ≃ Z) :
    ∀ᵐ ω ∂P, ∃ A B : Z → ℝ,
      (∀ x, Tendsto (fun n : ℕ =>
        (((Finset.range n).filter (fun i => precRel (lt ω) (e i) x)).card : ℝ) / n)
        atTop (𝓝 (A x))) ∧
      (∀ x, Tendsto (fun n : ℕ =>
        (((Finset.range n).filter (fun i => simRel (lt ω) (e i) x)).card : ℝ) / n)
        atTop (𝓝 (B x))) ∧
      ∀ x y : Z, (A x + B x / 2 = A y + B y / 2 ↔ simRel (lt ω) x y) ∧
        (A x + B x / 2 < A y + B y / 2 ↔ precRel (lt ω) x y) := by sorry

end PhyloCSP
