-- Prove2me | Theorems.Thm_RandLatEnum_Supplement_theorem_1_3
-- name    : RandLatEnum.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:03:35.483739+00:00
-- url     : https://prove2.me/theorems/39761104-9e2d-4064-93ee-2082d63046b5
-- title:
--   Theorem 1.3 — recursive binary splits give $T(B_{\mathrm{rec}})\le n^{c_{\mathrm{rec}}n+o(n)}$, $c_{\mathrm{rec}}<0.14740$
-- statement:
--   Let $L\sim\mu_n$. With probability $1-o(1)$, $L$ contains a chain of sublattices $\{0\}=M_0\subseteq M_1\subseteq\dots\subseteq M_r=L$ such that combining (lifted) HKZ and reversed dual-HKZ bases of the orthogonal quotients $\pi_{M_i^\perp}(M_{i+1})$ gives a basis of $L$ (at least one such combination exists), and every basis $B_{\mathrm{rec}}$ so obtained (any choice of the block bases and of the lifts) satisfies
--   $$T(B_{\mathrm{rec}})\le n^{c_{\mathrm{rec}}\,n+o(n)},\qquad c_{\mathrm{rec}}<0.14740.$$
--
--   The number of blocks $r$ and the orientation (HKZ or reversed dual-HKZ) of each block are fixed independently of $n$. This improves the two-block constant $c_2=0.15163\ldots$ of Theorem 1.2, and is within $0.001$ of the universal lower bound $c_{\mathrm{flat}}=(2-\sqrt2)/4$ of Theorem 1.5.
--
--   Differences from the source:
--   - encoding: L ∼ µ_n, the Haar probability measure on X_n = SL_n(ℝ)/SL_n(ℤ) → a family μ n of SL_n(ℝ)-invariant Borel probability measures on X n (hypothesis IsHaarLatticeMeasure), L = latticeOf x; reason: there is exactly one such measure (Siegel); same convention as the published goal RandLatEnum.theorem_1_5
--   - encoding: with probability 1 − o(1) → the outer µ_n-measure of the bad event tends to 0; reason: same convention as the published goal; equal to the probability for measurable events and never weaker
--   - encoding: o(n) in the exponent → one g : ℕ → ℝ with g(n)/n → 0, chosen before the lattice and the basis; reason: same convention as the published goal
--   - encoding: c_rec < 0.14740 (c_rec the numerically evaluated maximum 0.147399340499… of the depth-14 profile) → ∃ c < 14740/100000 with T ≤ n^{c n + g(n)}; reason: the theorem asserts only the strict numerical bound
--   - reading: a sequence of dense sublattices M0 ⊆ M1 ⊆ ⋯ ⊆ L with combined (lifted) HKZ / reversed dual-HKZ bases of the block quotients → a number of blocks r and orientations σ fixed before n; ranks 0 = κ_0 < ⋯ < κ_r = n depending on the lattice; a chain M_0 ⊆ ⋯ ⊆ M_r that is the prefix-span chain of some basis block-reduced along κ, σ, and the bound for every basis block-reduced along κ, σ whose prefix spans are the M_i; reason: "combining ... we obtain a basis" is read as in Theorem 1.2, for every such combination (the stronger reading; the proof bounds every leaf block by the deterministic Lemma 4.1, so it gives this); the proof uses one fixed finite tree (16384 blocks), so a fixed r is what is proved; "dense" is descriptive and carries no separate quantitative condition in the statement; a block count growing with n would make the block structure vacuous
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08adef70deb2f23a9a830e01c5a5b031ddaf5e0d4f88ce5174d67214b37), Theorem 1.3, (1.4), p.4 (proof §5.3, (5.21)–(5.23), p.25)

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_RandLatEnum_X
import Definitions.Def_RandLatEnum_latticeOf
import Definitions.Def_RandLatEnum_IsHaarLatticeMeasure
import Definitions.Def_RandLatEnum_treeSize
import Definitions.Def_RandLatEnum_Supplement_IsBlockReducedBasis

namespace RandLatEnum.Supplement

open MeasureTheory Filter Topology KannanLattice.Core RandLatEnum

/-- **Theorem 1.3 (Tree size of recursive binary splits)** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Theorem 1.3, (1.4), p.4;
proof §5.3, p.25). With probability `1 − o(1)`, `L ∼ µ_n` contains a sequence of dense sublattices
`M_0 ⊆ M_1 ⊆ ⋯ ⊆ L` such that, combining (lifted) HKZ and reversed dual-HKZ bases of (orthogonal
quotients of) these blocks, we obtain a basis `B_rec` of `L` with `T(B_rec) ≤ n^{c_rec·n + o(n)}`,
`c_rec < 0.14740`.

**Formalization Note.** `µ_n` is a family of `SL_n(ℝ)`-invariant Borel probability measures on `X_n` (unique, hence Haar); `L = latticeOf x`; bases are ordered `ℤ`-bases of `L` coerced to `ℝⁿ`. The `o(n)` is one function `g` with `g(n)/n → 0`, chosen before the lattice and the basis; "with probability `1 − o(1)`" is: the (outer) `µ_n`-measure of the bad event tends to `0`. `c_rec` is a numerically determined constant: the statement asserts
some `c < 0.14740`. The number of blocks `r` and their orientations `σ` (`true` = HKZ, `false` =
reversed dual-HKZ) are fixed before `n`, so the block structure has content; the ranks
`0 = κ_0 < ⋯ < κ_r = n` and the chain `M_0 ⊆ ⋯ ⊆ M_r` may depend on the lattice. The good event
is: some chain `M_i` (with ranks `κ_i`) is the prefix-span chain of a basis block-reduced along
`κ`, `σ`, and **every** basis block-reduced along `κ`, `σ` whose prefix spans are the `M_i` (any
HKZ / reversed dual-HKZ bases of the block quotients, any lifts) satisfies the tree bound, read
like Theorem 1.2 ("combining ... we obtain a basis"). -/
theorem theorem_1_3 (μ : ∀ n : ℕ, Measure (X n)) (hμ : ∀ n, IsHaarLatticeMeasure (μ n)) :
    ∃ c : ℝ, c < 14740 / 100000 ∧ ∃ (r : ℕ) (σ : Fin r → Bool),
      ∃ g : ℕ → ℝ, Tendsto (fun n : ℕ => g n / n) atTop (𝓝 0) ∧
        Tendsto (fun n : ℕ => μ n {x : X n | ¬ ∃ (κ : Fin (r + 1) → ℕ)
            (Ms : Fin (r + 1) → Submodule ℤ (EuclideanSpace ℝ (Fin n))),
            (∃ B : Module.Basis (Fin n) ℤ (latticeOf x),
              IsBlockReducedBasis r κ σ (fun l => (B l : EuclideanSpace ℝ (Fin n))) ∧
              ∀ i : Fin (r + 1), Submodule.span ℤ ((fun l => (B l : EuclideanSpace ℝ (Fin n))) ''
                {l : Fin n | (l : ℕ) < κ i}) = Ms i) ∧
            ∀ B : Module.Basis (Fin n) ℤ (latticeOf x),
              IsBlockReducedBasis r κ σ (fun l => (B l : EuclideanSpace ℝ (Fin n))) →
              (∀ i : Fin (r + 1), Submodule.span ℤ ((fun l => (B l : EuclideanSpace ℝ (Fin n))) ''
                {l : Fin n | (l : ℕ) < κ i}) = Ms i) →
              (treeSize (fun l => (B l : EuclideanSpace ℝ (Fin n)))
                  (lambdaOne (latticeOf x : Set (EuclideanSpace ℝ (Fin n)))) : ℝ) ≤
                (n : ℝ) ^ (c * n + g n)}) atTop (𝓝 0) := by sorry

end RandLatEnum.Supplement
