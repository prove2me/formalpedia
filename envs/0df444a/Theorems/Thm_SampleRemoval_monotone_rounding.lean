-- Prove2me | Theorems.Thm_SampleRemoval_monotone_rounding
-- name    : SampleRemoval.monotone_rounding
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T05:19:30.722498+00:00
-- url     : https://prove2.me/theorems/c6569394-a6ee-45ea-a37d-65b596c7ad63
-- title:
--   Theorem 3.3 (Monotone rounding) — in general position, $s_{\mathrm{frac}}\le s_{\mathrm{int}}<s_{\mathrm{frac}}+d$
-- statement:
--   Let $(x_i,y_i)\in\mathbb R^d\times\mathbb R$, $i\in[n]$, be observations whose design $x_1,\dots,x_n$ is in general position, and let $(e,\theta)$ be a target, $\langle e,\beta([n])\rangle>\theta$, with feasible set $\mathcal W=\{w\in[0,1]^n:G(w)\succ0,\ \langle e,\beta(w)\rangle\le\theta\}$, integral stability $s_{\mathrm{int}}=\min\{n-|S|:\mathbf 1_S\in\mathcal W\}$ and fractional stability $s_{\mathrm{frac}}=\inf\{n-\|w\|_1:w\in\mathcal W\}$.
--
--   1. If $\mathcal W\neq\emptyset$ and $n-s_{\mathrm{frac}}>d-1$, then $s_{\mathrm{frac}}$ is attained.
--   2. If $\mathcal W$ contains some $w$ with $\|w\|_1\ge2d$, then $s_{\mathrm{frac}}$ is attained, some indicator $\mathbf 1_S$ lies in $\mathcal W$, and
--   $$
--   s_{\mathrm{frac}}\le s_{\mathrm{int}}<s_{\mathrm{frac}}+d,\qquad\text{equivalently}\qquad \lceil s_{\mathrm{frac}}\rceil\le s_{\mathrm{int}}\le\lceil s_{\mathrm{frac}}\rceil+d-1 .
--   $$
--   Moreover, every $w\in\mathcal W$ with $\|w\|_1\ge2d$ rounds to a set $S$ with $\mathbf 1_S\in\mathcal W$ and
--   $$
--   n-|S|<n-\|w\|_1+d .
--   $$
--
--   The integral stability, a minimum over the $2^n$ subsets of the sample, is thus pinned to one of $d$ consecutive integers determined by the fractional stability; for $d=1$ it equals $\lceil s_{\mathrm{frac}}\rceil$, and for simple regression with an intercept it takes one of two values. Any heavy fractional certificate also yields an explicit deletion set.
--
--   Differences from the source:
--
--   - encoding: observations (x_i, y_i) ∈ ℝᵈ × ℝ indexed by i ∈ [n] → x : Fin n → Fin d → ℝ, y : Fin n → ℝ, paper index i = Lean index i − 1; reason: Lean convention; same instances
--   - encoding: ∥w∥₁ → ∑ i, w i; reason: every weight lies in [0, 1], so the sum of the coordinates is the ℓ¹ norm
--   - reading: one linear program, one d × d inversion and O(d) rank-one updates produce S with 1_S ∈ 𝒲 and n − |S| < n − ∥w∥₁ + d → there exists S with 1_S ∈ 𝒲 and n − |S| < n − ∥w∥₁ + d; reason: the paper fixes no model of computation; the construction (one LP vertex, then single-coordinate roundings) is carried by the milestones Lemma 3.2 and the Rounding step
--   - encoding: inf over 𝒲 (= +∞ when 𝒲 = ∅) in "s_frac is attained whenever n − s_frac > d − 1" → hypothesis 𝒲.Nonempty in clause (a); reason: Lean's sInf ∅ = 0; the hypothesis excludes only the case where the source's hypothesis already fails
--   - encoding: s_int = min{n − |S| : 1_S ∈ 𝒲} → sInf in ℕ, with the conclusion ∃ S, 1_S ∈ 𝒲 asserted alongside; reason: Definition 2.1's min presupposes that some 1_S lies in 𝒲; the conjunct makes sInf the minimum
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Theorem 3.3, pp.4–5 (PDF pp.6–7); proof p.5

import Mathlib
import Definitions.Def_SampleRemoval_ind
import Definitions.Def_SampleRemoval_feasible
import Definitions.Def_SampleRemoval_sInt
import Definitions.Def_SampleRemoval_sFrac
import Definitions.Def_SampleRemoval_GeneralPosition
import Definitions.Def_SampleRemoval_IsTarget

set_option autoImplicit false

namespace SampleRemoval

/-- **Theorem 3.3 (Monotone rounding)** (Xu, Gao, Hu, *Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares*, STOC 2027 submission (manuscript sha256 dcd33ace…), pp.4–5). Assume GP and that `𝒲` contains some `w`
with `∥w∥₁ ≥ 2d`. Then `s_frac` is attained, and
`s_frac ≤ s_int < s_frac + d`, equivalently `⌈s_frac⌉ ≤ s_int ≤ ⌈s_frac⌉ + d − 1`.
Moreover, given any `w ∈ 𝒲` with `∥w∥₁ ≥ 2d`, one linear program, one `d × d` inversion and
`O(d)` rank-one updates produce `S` with `1_S ∈ 𝒲` and `n − |S| < n − ∥w∥₁ + d`. More generally,
`s_frac` is attained whenever `n − s_frac > d − 1`.

For every design in general position and every target `(e, θ)`:
(a) if `𝒲 ≠ ∅` and `n − s_frac > d − 1`, then `s_frac` is attained;
(b) if some `w ∈ 𝒲` has `∥w∥₁ ≥ 2d`, then `s_frac` is attained, some indicator `1_S` lies in
`𝒲` (so `s_int` is a minimum), `s_frac ≤ s_int < s_frac + d`, `⌈s_frac⌉ ≤ s_int ≤ ⌈s_frac⌉ + d − 1`,
and every `w ∈ 𝒲` with `∥w∥₁ ≥ 2d` rounds to some `1_S ∈ 𝒲` with `n − |S| < n − ∥w∥₁ + d`.

**Formalization Note** "One linear program, one d × d inversion and O(d) rank-one updates
produce S" is stated as the existence of `S` (no model of computation is fixed). `𝒲.Nonempty`
in (a) and `∃ S, 1_S ∈ 𝒲` in (b) make Lean's `sInf` encodings of `s_frac` and `s_int` the
paper's infimum and minimum. `∥w∥₁` is `∑ i, w i`. Differences `n − ·` are taken in `ℝ` and
the ceiling bound in `ℤ`. -/
theorem monotone_rounding {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (e : Fin d → ℝ)
    (θ : ℝ) (hGP : GeneralPosition x) (hT : IsTarget x y e θ) :
    ((feasible x y e θ).Nonempty → (d : ℝ) - 1 < n - sFrac x y e θ →
        ∃ w ∈ feasible x y e θ, (n : ℝ) - ∑ i, w i = sFrac x y e θ) ∧
      ((∃ w ∈ feasible x y e θ, 2 * (d : ℝ) ≤ ∑ i, w i) →
        (∃ w ∈ feasible x y e θ, (n : ℝ) - ∑ i, w i = sFrac x y e θ) ∧
        (∃ S : Finset (Fin n), ind S ∈ feasible x y e θ) ∧
        sFrac x y e θ ≤ (sInt x y e θ : ℝ) ∧
        (sInt x y e θ : ℝ) < sFrac x y e θ + d ∧
        ⌈sFrac x y e θ⌉ ≤ (sInt x y e θ : ℤ) ∧
        (sInt x y e θ : ℤ) ≤ ⌈sFrac x y e θ⌉ + d - 1 ∧
        ∀ w ∈ feasible x y e θ, 2 * (d : ℝ) ≤ ∑ i, w i →
          ∃ S : Finset (Fin n), ind S ∈ feasible x y e θ ∧
            (n : ℝ) - S.card < n - ∑ i, w i + d) := by sorry

end SampleRemoval
