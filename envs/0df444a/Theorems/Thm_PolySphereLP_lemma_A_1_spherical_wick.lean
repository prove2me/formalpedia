-- Prove2me | Theorems.Thm_PolySphereLP_lemma_A_1_spherical_wick
-- name    : PolySphereLP.lemma_A_1_spherical_wick
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:24.590881+00:00
-- url     : https://prove2.me/theorems/8aaebc8d-8f07-4a50-9267-12147128bba4
-- title:
--   Lemma A.1 — spherical Wick formula
-- statement:
--   Let $n\ge2$, let $m\ge0$ be an integer, and let $\sigma$ be the uniform probability measure on $S^{n-1}$. Write $\mathcal P_2(2m)$ for the partitions of $[2m]$ into unordered pairs. Then:
--   1. for any indices $i_1,\dots,i_{2m}\in[n]$,
--   $$\int x_{i_1}\cdots x_{i_{2m}}\,d\sigma(x)=\frac1{\mathrm R_{n,m}}\sum_{\pi\in\mathcal P_2(2m)}\prod_{\{s,t\}\in\pi}\delta_{i_s,i_t};$$
--   2. for real vectors $v_1,\dots,v_{2m}\in\mathbb R^n$,
--   $$\int\prod_{s=1}^{2m}\langle v_s,x\rangle\,d\sigma(x)=\frac1{\mathrm R_{n,m}}\sum_{\pi\in\mathcal P_2(2m)}\prod_{\{s,t\}\in\pi}\langle v_s,v_t\rangle;$$
--   3. all odd moments vanish: the integrals of $x_{i_1}\cdots x_{i_{2m+1}}$ and of $\prod_{s=1}^{2m+1}\langle v_s,x\rangle$ are $0$.
--
--   At $m=0$ the partition set contains only the empty partition and the empty product is $1$.
--
--   This is the basic moment computation on the sphere; it gives the spherical–tensor inner-product identity (Lemma 2.1) and the normalization $\mathrm R_{n,m}$ used throughout.
--
--   **Formalization Note** Pair partitions are the published `FeynmanWick.pairings m` (fixed-point-free involutions of $\{0,\dots,2m-1\}$), with one factor per pair.
--
--   Differences from the source:
--   - encoding: partitions of [2m] into unordered pairs, product over the pairs {s,t} → fixed-point-free involutions π of Fin (2m) (FeynmanWick.pairings), product over s with s < π s; reason: the two are in bijection and give the same sum
--   - encoding: indices in [n] = {1,…,n} → indices in Fin n = {0,…,n−1}; reason: Lean convention; relabelling only
--   - reading: "All corresponding odd moments vanish" → both the coordinate and the vector form with 2m+1 factors integrate to 0; reason: "corresponding" refers to the two displayed forms
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), Lemma A.1, p.23, eq. (52)

import Mathlib
import Definitions.Def_SphereSOS_Rate_SphereMeasure
import Definitions.Def_FeynmanWickPairings
import Definitions.Def_PolySphereLP_Rmom
open MvPolynomial MeasureTheory

namespace PolySphereLP

/-- **Lemma A.1 (Spherical Wick formula).** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), Lemma A.1, p.23, eq. (52).

Let `n ≥ 2`, `m ≥ 0`, and `σ` the uniform probability measure on `S^{n−1}`. For all indices
`i₁,…,i_{2m} ∈ [n]`, `∫ x_{i₁}⋯x_{i_{2m}} dσ = (1/R_{n,m}) ∑_{π ∈ 𝒫₂(2m)} ∏_{{s,t}∈π} δ_{i_s,i_t}`;
for vectors `v₁,…,v_{2m} ∈ ℝⁿ`, `∫ ∏ₛ ⟨vₛ, x⟩ dσ = (1/R_{n,m}) ∑_π ∏_{{s,t}∈π} ⟨vₛ, v_t⟩`; and all odd
moments (an odd number `2m+1` of factors) vanish, in both forms.

**Formalization Note.** `𝒫₂(2m)` is the published `FeynmanWick.pairings m` (fixed-point-free
involutions of `Fin (2m)`), and `FeynmanWick.wickSum W = ∑_π ∏_{s < π s} W s (π s)`, one factor per
pair. At `m = 0` the only pairing is the empty one and the empty product is `1`, which is the
paper's convention. The integrands are polynomials, integrable against `σ`. -/
theorem lemma_A_1_spherical_wick (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    (∀ i : Fin (2 * m) → Fin n,
      ∫ x, ∏ s, x (i s) ∂(SphereSOS.Rate.sigma n) =
        1 / Rmom n m * FeynmanWick.wickSum (fun s t => if i s = i t then (1 : ℝ) else 0)) ∧
    (∀ v : Fin (2 * m) → Fin n → ℝ,
      ∫ x, ∏ s, (∑ l, v s l * x l) ∂(SphereSOS.Rate.sigma n) =
        1 / Rmom n m * FeynmanWick.wickSum (fun s t => ∑ l, v s l * v t l)) ∧
    (∀ i : Fin (2 * m + 1) → Fin n, ∫ x, ∏ s, x (i s) ∂(SphereSOS.Rate.sigma n) = 0) ∧
    (∀ v : Fin (2 * m + 1) → Fin n → ℝ,
      ∫ x, ∏ s, (∑ l, v s l * x l) ∂(SphereSOS.Rate.sigma n) = 0) := by sorry

end PolySphereLP
