-- Prove2me | Theorems.Thm_RandLatEnum_lemma_2_1
-- name    : RandLatEnum.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:32.552942+00:00
-- url     : https://prove2.me/theorems/49acf70f-56c6-40eb-95a6-c164d5fa0889
-- title:
--   Lemma 2.1 — $\lambda_1(L)/(\det L)^{1/d}\le 2r_d\le\sqrt d$ and $\ln r_d=\frac12\ln\frac{d}{2\pi e}+o(1)$
-- statement:
--   For every $d\ge1$ and every lattice $L$ of rank $d$,
--   $$
--   \frac{\lambda_1(L)}{(\det L)^{1/d}}\le 2r_d\le\sqrt d ,
--   $$
--   where $\lambda_1(L)$ is the length of a shortest nonzero vector, $\det L$ the covolume of $L$ in its span and $r_d=V_d^{-1/d}$ the radius of the ball of volume one. Moreover, as $d\to\infty$,
--   $$
--   \ln r_d=\frac12\ln\frac{d}{2\pi e}+o(1).
--   $$
--
--   The first inequality is Minkowski's bound on the shortest vector; the second makes it explicit; the asymptotic fixes the scale $\lambda_1\approx\sqrt{d/(2\pi e)}$ used throughout the tree-size estimates.
--
--   **Formalization Note** A rank-$d$ lattice is the $\mathbb Z$-span of a linearly independent family $b_1,\dots,b_d$ in some $\mathbb R^k$; $\det L$ is the product of its Gram–Schmidt lengths and $\lambda_1$ the infimum of the norms of its nonzero vectors.
--
--   Differences from the source:
--   - encoding: a rank-d lattice L, det L, λ₁(L) → the ℤ-span of a linearly independent b : Fin d → ℝᵏ (any k), det = product of Gram–Schmidt lengths, λ₁ = infimum of nonzero norms; reason: standard representation; the same lattices and quantities
--   - encoding: ln r_d = ½ ln(d/(2πe)) + o(1) as d → ∞ → ln r_d − ½ ln(d/(2πe)) → 0 along d ∈ ℕ; reason: definition of o(1)
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Lemma 2.1, (2.6), p.15

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_RandLatEnum_rGH

namespace RandLatEnum

open Filter Topology KannanLattice.Core

/-- **Lemma 2.1 (Geometric bounds)** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Lemma 2.1, (2.6), p.15). For every rank-`d` lattice
`L`, `λ₁(L)/(det L)^{1/d} ≤ 2r_d ≤ √d`, and `ln r_d = ½ ln(d/(2πe)) + o(1)` as `d → ∞`.

**Formalization Note.** A rank-`d` lattice is the `ℤ`-span of a linearly independent family
`b : Fin d → ℝᵏ` in any ambient dimension `k`; `det L` is the product of the Gram–Schmidt lengths
(its covolume in its span) and `λ₁` the infimum of the nonzero norms. `d ≥ 1` as in (2.5). The
asymptotic is a limit over `d ∈ ℕ`. -/
theorem lemma_2_1 :
    (∀ (d k : ℕ) (b : Fin d → EuclideanSpace ℝ (Fin k)), 1 ≤ d → LinearIndependent ℝ b →
      lambdaOne (lattice b : Set (EuclideanSpace ℝ (Fin k))) / latticeDet b ^ ((1 : ℝ) / d)
          ≤ 2 * rGH d ∧
        2 * rGH d ≤ Real.sqrt d) ∧
    Tendsto (fun d : ℕ => Real.log (rGH d) - 1 / 2 * Real.log (d / (2 * Real.pi * Real.exp 1)))
      atTop (𝓝 0) := by sorry

end RandLatEnum
