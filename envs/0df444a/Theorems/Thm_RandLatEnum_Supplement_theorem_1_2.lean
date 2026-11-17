-- Prove2me | Theorems.Thm_RandLatEnum_Supplement_theorem_1_2
-- name    : RandLatEnum.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:02:54.214142+00:00
-- url     : https://prove2.me/theorems/438e244c-2504-4073-b161-5c9c702ff404
-- title:
--   Theorem 1.2 — a two-block split gives $T(B_2)=n^{n/(4\sqrt e)+o(n)}$
-- statement:
--   Let $L\sim\mu_n$ and $m=\lfloor (n-1)/2\rfloor$. With probability $1-o(1)$:
--
--   1. $L$ has a primitive sublattice $M$ of rank $m$ with $\det M\le e^{O(n)}n^{n/8}$;
--   2. combining a reversed dual-HKZ basis of $M$ with lifts of an HKZ basis of its orthogonal quotient $\pi_{M^\perp}(L)$ gives a basis $B_2$ of $L$ with
--   $$T(B_2)=n^{c_2\,n+o(n)},\qquad c_2=\frac1{4\sqrt e}=0.15163\ldots$$
--
--   Here $T$ is the enumeration tree size at radius $\lambda_1(L)$, the $e^{O(n)}$ constant does not depend on $n$, and the tree-size estimate holds for every such combination over $M$. Since $c_2<c_{\mathrm{HKZ}}=1/(2e)$, this shows that quasi-HKZ bases are asymptotically suboptimal for enumeration on random lattices.
--
--   Differences from the source:
--   - encoding: L ∼ µ_n, the Haar probability measure on X_n = SL_n(ℝ)/SL_n(ℤ) → a family μ n of SL_n(ℝ)-invariant Borel probability measures on X n (hypothesis IsHaarLatticeMeasure), L = latticeOf x; reason: there is exactly one such measure (Siegel); same convention as the published goal RandLatEnum.theorem_1_5
--   - encoding: with probability 1 − o(1) → the outer µ_n-measure of the bad event tends to 0; reason: same convention as the published goal; equal to the probability for measurable events and never weaker
--   - encoding: = n^{c n + o(n)} → one g : ℕ → ℝ with g(n)/n → 0, chosen before the lattice and the basis, and n^{c n − g(n)} ≤ T ≤ n^{c n + g(n)}; reason: one g for both sides is equivalent to two o(n) terms (take the larger in absolute value)
--   - encoding: det M ≤ e^{O(n)} n^{n/8} → one constant C, chosen before n, with subDet M ≤ exp(C n) · n^{n/8}; reason: an O(n) upper bound in the exponent is a constant multiple of n
--   - reading: combining a reversed dual-HKZ basis of M with lifts of an HKZ basis of its orthogonal quotient gives a basis B2 with T(B2) = n^{c2 n + o(n)} → for the M found, a two-block basis of L over M exists, and every two-block basis over M (any reversed dual-HKZ basis of M, any HKZ basis of the quotient, any lifts) satisfies the two-sided bound; reason: the stronger of the two readings ("a" combination vs "every" combination); the proof applies Proposition 4.3, which holds simultaneously for all quasi-HKZ bases, and T depends only on the projections, not the lifts
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08adef70deb2f23a9a830e01c5a5b031ddaf5e0d4f88ce5174d67214b37), Theorem 1.2, (1.3), p.4 (proof §5.2, (5.14)–(5.16), p.24)

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_RandLatEnum_X
import Definitions.Def_RandLatEnum_latticeOf
import Definitions.Def_RandLatEnum_IsHaarLatticeMeasure
import Definitions.Def_RandLatEnum_treeSize
import Definitions.Def_RandLatEnum_IsPrimitiveSub
import Definitions.Def_RandLatEnum_subDet
import Definitions.Def_RandLatEnum_Supplement_IsTwoBlockBasis

namespace RandLatEnum.Supplement

open MeasureTheory Filter Topology KannanLattice.Core RandLatEnum

/-- **Theorem 1.2 (Tree size of a two-block split)** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Theorem 1.2, (1.3), p.4; proof
§5.2, p.24). With probability `1 − o(1)`, `L ∼ µ_n` has a primitive sublattice `M` of rank
`m = ⌊(n−1)/2⌋` with `det M ≤ e^{O(n)} n^{n/8}`. Combining a reversed dual-HKZ basis of `M` with
lifts of an HKZ basis of its orthogonal quotient gives a basis `B_2` of `L` with enumeration tree
size `T(B_2) = n^{c_2·n + o(n)}`, `c_2 = 1/(4√e)`.

**Formalization Note.** `µ_n` is a family of `SL_n(ℝ)`-invariant Borel probability measures on `X_n` (unique, hence Haar); `L = latticeOf x`; bases are ordered `ℤ`-bases of `L` coerced to `ℝⁿ`. The `o(n)` is one function `g` with `g(n)/n → 0`, chosen before the lattice and the basis; "with probability `1 − o(1)`" is: the (outer) `µ_n`-measure of the bad event tends to `0`. The `e^{O(n)}` is one constant `C`, chosen before `n`, with
`det M ≤ e^{Cn} n^{n/8}` (published `subDet`). The good event is: some primitive rank-`m`
sublattice `M` with that bound admits a two-block basis (`IsTwoBlockBasis m M`), and **every**
two-block basis over `M` (any reversed dual-HKZ basis of `M`, any HKZ basis of the quotient, any
lifts) satisfies `n^{c_2 n − g(n)} ≤ T(B) ≤ n^{c_2 n + g(n)}`. `m = (n − 1)/2` in `ℕ` is the floor. -/
theorem theorem_1_2 (μ : ∀ n : ℕ, Measure (X n)) (hμ : ∀ n, IsHaarLatticeMeasure (μ n)) :
    ∃ C : ℝ, ∃ g : ℕ → ℝ, Tendsto (fun n : ℕ => g n / n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => μ n {x : X n | ¬ ∃ M : Submodule ℤ (EuclideanSpace ℝ (Fin n)),
          IsPrimitiveSub (latticeOf x) M ∧ Module.finrank ℤ M = (n - 1) / 2 ∧
          subDet M ≤ Real.exp (C * n) * (n : ℝ) ^ ((n : ℝ) / 8) ∧
          (∃ B : Module.Basis (Fin n) ℤ (latticeOf x),
            IsTwoBlockBasis ((n - 1) / 2) M (fun i => (B i : EuclideanSpace ℝ (Fin n)))) ∧
          ∀ B : Module.Basis (Fin n) ℤ (latticeOf x),
            IsTwoBlockBasis ((n - 1) / 2) M (fun i => (B i : EuclideanSpace ℝ (Fin n))) →
              (n : ℝ) ^ (1 / (4 * Real.sqrt (Real.exp 1)) * n - g n) ≤
                  (treeSize (fun i => (B i : EuclideanSpace ℝ (Fin n)))
                    (lambdaOne (latticeOf x : Set (EuclideanSpace ℝ (Fin n)))) : ℝ) ∧
                (treeSize (fun i => (B i : EuclideanSpace ℝ (Fin n)))
                    (lambdaOne (latticeOf x : Set (EuclideanSpace ℝ (Fin n)))) : ℝ) ≤
                  (n : ℝ) ^ (1 / (4 * Real.sqrt (Real.exp 1)) * n + g n)}) atTop (𝓝 0) := by sorry

end RandLatEnum.Supplement
