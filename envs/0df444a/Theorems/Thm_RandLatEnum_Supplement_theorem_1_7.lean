-- Prove2me | Theorems.Thm_RandLatEnum_Supplement_theorem_1_7
-- name    : RandLatEnum.Supplement.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:05:45.741449+00:00
-- url     : https://prove2.me/theorems/d0cd94fb-f758-4999-8bce-b6cf938ff72b
-- title:
--   Theorem 1.7 — a two-block basis has $\sqrt{P(B_2)}\le n^{\tau_2 n+o(n)}$, $\tau_2=1/(4\sqrt e)-1/16$
-- statement:
--   Let $L\sim\mu_n$ and let $P(B)=\prod_{i=1}^n\max\{1,a_i^{-1}\}$ be the Feng–Gao–Liu geometric product of a basis $B$. With probability $1-o(1)$, $L$ contains a basis $B_2$ (a two-block basis over a primitive sublattice of rank $\lfloor (n-1)/2\rfloor$, as in Theorem 1.2) with
--   $$\sqrt{P(B_2)}\ \le\ n^{\tau_2\,n+o(n)},\qquad \tau_2=\frac1{4\sqrt e}-\frac1{16}=0.08913\ldots$$
--
--   This improves the quasi-HKZ value $\tau_{\mathrm{HKZ}}=1/(4e)=0.09196\ldots$ of Feng–Gao–Liu.
--
--   Differences from the source:
--   - encoding: L ∼ µ_n, the Haar probability measure on X_n = SL_n(ℝ)/SL_n(ℤ) → a family μ n of SL_n(ℝ)-invariant Borel probability measures on X n (hypothesis IsHaarLatticeMeasure), L = latticeOf x; reason: there is exactly one such measure (Siegel); same convention as the published goal RandLatEnum.theorem_1_5
--   - encoding: with probability 1 − o(1) → the outer µ_n-measure of the bad event tends to 0; reason: same convention as the published goal; equal to the probability for measurable events and never weaker
--   - encoding: o(n) in the exponent → one g : ℕ → ℝ with g(n)/n → 0, chosen before the lattice and the basis; reason: same convention as the published goal
--   - reading: L contains a basis B2 with √P(B2) ≤ n^{τ2 n + o(n)} → L has a basis that is a two-block basis (IsTwoBlockBasis ⌊(n−1)/2⌋ M, M the ℤ-span of its first ⌊(n−1)/2⌋ vectors) with √P ≤ n^{τ2 n + g(n)}; reason: B2 names the two-block basis of Theorem 1.2 (title "of a two-block split"); this is the stronger reading and implies the literal one by dropping the two-block clause; the matching lower bound in the proof is not part of the theorem
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08adef70deb2f23a9a830e01c5a5b031ddaf5e0d4f88ce5174d67214b37), Theorem 1.7, (1.10), p.6 (proof §8.2, (8.6)–(8.7), p.32)

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_RandLatEnum_X
import Definitions.Def_RandLatEnum_latticeOf
import Definitions.Def_RandLatEnum_IsHaarLatticeMeasure
import Definitions.Def_RandLatEnum_Supplement_fglProduct
import Definitions.Def_RandLatEnum_Supplement_IsTwoBlockBasis

namespace RandLatEnum.Supplement

open MeasureTheory Filter Topology KannanLattice.Core RandLatEnum

/-- **Theorem 1.7 (Collision search cost factor of a two-block split)** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Theorem 1.7,
(1.10), p.6; proof §8.2, p.32). With probability `1 − o(1)`, `L ∼ µ_n` contains a basis `B_2` with
FGL costs `√P(B_2) ≤ n^{τ_2·n + o(n)}`, `τ_2 = 1/(4√e) − 1/16`.

**Formalization Note.** `µ_n` is a family of `SL_n(ℝ)`-invariant Borel probability measures on `X_n` (unique, hence Haar); `L = latticeOf x`; bases are ordered `ℤ`-bases of `L` coerced to `ℝⁿ`. The `o(n)` is one function `g` with `g(n)/n → 0`, chosen before the lattice and the basis; "with probability `1 − o(1)`" is: the (outer) `µ_n`-measure of the bad event tends to `0`. `B_2` is read as the two-block basis of Theorem 1.2 (title and
notation): the good event is that some basis of `L` is a two-block basis (`IsTwoBlockBasis m M`,
`m = ⌊(n−1)/2⌋`, `M` the `ℤ`-span of its first `m` vectors) with the upper bound. Dropping the
two-block clause gives the literal "L contains a basis with `√P ≤ n^{τ_2 n + o(n)}`"; the matching
lower bound obtained in the proof is not part of the theorem. `P(B)` is `fglProduct` ((8.4), p.31). -/
theorem theorem_1_7 (μ : ∀ n : ℕ, Measure (X n)) (hμ : ∀ n, IsHaarLatticeMeasure (μ n)) :
    ∃ g : ℕ → ℝ, Tendsto (fun n : ℕ => g n / n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => μ n {x : X n | ¬ ∃ (B : Module.Basis (Fin n) ℤ (latticeOf x))
          (M : Submodule ℤ (EuclideanSpace ℝ (Fin n))),
          IsTwoBlockBasis ((n - 1) / 2) M (fun i => (B i : EuclideanSpace ℝ (Fin n))) ∧
          Real.sqrt (fglProduct (fun i => (B i : EuclideanSpace ℝ (Fin n)))) ≤
            (n : ℝ) ^ ((1 / (4 * Real.sqrt (Real.exp 1)) - 1 / 16) * n + g n)}) atTop (𝓝 0) := by sorry

end RandLatEnum.Supplement
