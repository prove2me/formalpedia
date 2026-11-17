-- Prove2me | Theorems.Thm_RandLatEnum_Supplement_theorem_1_4
-- name    : RandLatEnum.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:04:23.601671+00:00
-- url     : https://prove2.me/theorems/b1a829aa-7670-4111-a86d-12bf38c1264e
-- title:
--   Theorem 1.4 — under Assumption 1, $T(B)\le n^{(c_{\mathrm{flat}}+\varepsilon)n+o(n)}$
-- statement:
--   Suppose Assumption 1 (first-moment sufficiency, in its precise form (6.2)–(6.3)) holds, and let $\varepsilon>0$ be fixed. Then with probability $1-o(1)$ as $n\to\infty$, $L\sim\mu_n$ contains a basis $B$ with
--   $$T(B)\le n^{(c_{\mathrm{flat}}+\varepsilon)\,n+o(n)},\qquad c_{\mathrm{flat}}=\frac{2-\sqrt2}{4}=0.14644\ldots$$
--
--   Together with the lower bound of Theorem 1.5, this shows that, under the heuristic assumption, $c_{\mathrm{flat}}$ is the optimal tree-size exponent over all bases of a random lattice.
--
--   Differences from the source:
--   - encoding: L ∼ µ_n, the Haar probability measure on X_n = SL_n(ℝ)/SL_n(ℤ) → a family μ n of SL_n(ℝ)-invariant Borel probability measures on X n (hypothesis IsHaarLatticeMeasure), L = latticeOf x; reason: there is exactly one such measure (Siegel); same convention as the published goal RandLatEnum.theorem_1_5
--   - encoding: with probability 1 − o(1) → the outer µ_n-measure of the bad event tends to 0; reason: same convention as the published goal; equal to the probability for measurable events and never weaker
--   - encoding: o(n) in the exponent → one g : ℕ → ℝ with g(n)/n → 0, chosen before the lattice and the basis; reason: same convention as the published goal
--   - encoding: Assumption 1 (precise form, (6.2)–(6.3)); P{C_n(L) > 0} = 1 − o(1); E_{µ_n}[C_{J,n}(L)] → hypothesis Assumption1 μ; µ_n{C_n(L) = 0} → 0; lower Lebesgue integrals ∫⁻ of the ℕ∞-valued counts; reason: Lean conventions of the published Eq. (7.3); the same statement for measurable counts
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08adef70deb2f23a9a830e01c5a5b031ddaf5e0d4f88ce5174d67214b37), Theorem 1.4, (1.5), p.5 (Assumption 1 precise form §6, (6.2)–(6.3), p.26; proof p.27)

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_RandLatEnum_X
import Definitions.Def_RandLatEnum_latticeOf
import Definitions.Def_RandLatEnum_IsHaarLatticeMeasure
import Definitions.Def_RandLatEnum_treeSize
import Definitions.Def_RandLatEnum_cFlat
import Definitions.Def_RandLatEnum_Supplement_Assumption1

namespace RandLatEnum.Supplement

open MeasureTheory Filter Topology KannanLattice.Core RandLatEnum

/-- **Theorem 1.4 (Tree size of improved heuristic splits)** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Theorem 1.4, (1.5), p.5;
proof §6, p.27). Suppose Assumption 1 holds, and let `ε > 0` be fixed. Then with probability
`1 − o(1)` as `n → ∞`, `L ∼ µ_n` contains a basis `B` with `T(B) ≤ n^{(c_flat+ε)·n + o(n)}`,
`c_flat = (2 − √2)/4`.

**Formalization Note.** `µ_n` is a family of `SL_n(ℝ)`-invariant Borel probability measures on `X_n` (unique, hence Haar); `L = latticeOf x`; bases are ordered `ℤ`-bases of `L` coerced to `ℝⁿ`. The `o(n)` is one function `g` with `g(n)/n → 0`, chosen before the lattice and the basis; "with probability `1 − o(1)`" is: the (outer) `µ_n`-measure of the bad event tends to `0`. Assumption 1 is its precise form (6.2)–(6.3), p.26
(`Assumption1 μ`), a hypothesis. `g` may depend on `ε`. `c_flat` is the published `cFlat`. -/
theorem theorem_1_4 (μ : ∀ n : ℕ, Measure (X n)) (hμ : ∀ n, IsHaarLatticeMeasure (μ n))
    (hA : Assumption1 μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℕ → ℝ, Tendsto (fun n : ℕ => g n / n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => μ n {x : X n | ¬ ∃ B : Module.Basis (Fin n) ℤ (latticeOf x),
          (treeSize (fun i => (B i : EuclideanSpace ℝ (Fin n)))
              (lambdaOne (latticeOf x : Set (EuclideanSpace ℝ (Fin n)))) : ℝ) ≤
            (n : ℝ) ^ ((cFlat + ε) * n + g n)}) atTop (𝓝 0) := by sorry

end RandLatEnum.Supplement
