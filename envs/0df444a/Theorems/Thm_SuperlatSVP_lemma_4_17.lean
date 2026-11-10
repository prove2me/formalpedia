-- Prove2me | Theorems.Thm_SuperlatSVP_lemma_4_17
-- name    : SuperlatSVP.lemma_4_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:46:22.179531+00:00
-- url     : https://prove2.me/theorems/cc82ecfe-559a-4793-9cbc-1e6734cc8991
-- title:
--   Lemma 4.17 — cap-overlap sum $\le(4b^2(1-u)^2/3)^{n/2}2^{o(n)}$
-- statement:
--   Let $\beta\ge0$, $b=2^\beta$, and let $A_n>0$ be a prefactor sequence with $\log_2A_n/n\to0$. There is a function $g$ with $g(n)/n\to0$ such that the following holds for every $n\ge1$. Let $L=B\mathbb Z^n$ be a full-rank lattice satisfying the point-count bound (2.3), $N_L(r\lambda_1(L))\le A_nb^nr^n$ for $r\ge1$, and let $\lambda_1(L)\le\lambda\le(1+n^{-2})\lambda_1(L)$. Then for every unit vector $s$ and every $3/16\le u\le0.4$,
--   $$\frac1{\operatorname{vol}(A)}\sum_{v\in L\setminus\{0\}}\operatorname{vol}\big(H_s(u)\cap(H_s(u)+v)\big)\le\left(\frac{4b^2(1-u)^2}3\right)^{n/2}2^{g(n)},$$
--   where $H_s(u)=\{x\in H:\langle s,x\rangle\ge\sqrt u\|x\|\}$ is the filter cap of the target shell and $A$ is the midpoint shell.
--
--   This bounds the expected number of colliding pairs inside one spherical filter. It is what makes the filtered final search cost $2^{f_{\rm filt}(S)n+o(n)}$ in Theorem 4.14.
--
--   **Formalization Note** The factor $2^{o(n)}$ is $2^{g(n)}$ for one $g$, which may depend on $\beta$ and $A$ but is fixed before $n$, $L$, $\lambda$, $s$ and $u$.
--
--   Differences from the source:
--   - generalization: the §4.1 standing assumptions det L = 1 and b ≥ √(4/3) → any full-rank lattice and any β ≥ 0; reason: both sides are invariant under scaling L and λ together, and the proof does not use b ≥ √(4/3); the source's case is an instance
--   - encoding: the factor 2^{o(n)} and (2.3) with A_n = 2^{o(n)} → 2^{g(n)} with g(n)/n → 0 fixed before the instance; A_n > 0 with log₂A_n/n → 0; reason: the source's definition of 2^{o(n)} (p.87) with uniform constants (p.14)
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §4.3, p.45 (PDF p.45), Lemma 4.17

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_SuperlatSVP_shellA

open MeasureTheory Filter
open scoped ENNReal

namespace SuperlatSVP

/-- Lemma 4.17 (Cap-overlap sum). Hhan, Kim, Kim, Laarhoven, *Superlattice methods for the shortest vector problem and discrete
Gaussian sampling*, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §4.3, p.45 (PDF p.45): "Assume λ1(L) ≤ λ ≤ (1 + n^{−2})λ1(L)
and (2.3), with b = 2^β. Uniformly over unit vectors s and 3/16 ≤ u ≤ 0.4,
(1/vol(A)) Σ_{v∈L∖{0}} vol(Hs(u) ∩ (Hs(u) + v)) ≤ (4b²(1 − u)²/3)^{n/2} 2^{o(n)}."

**Formalization Note.** (2.3) is a family condition: `β ≥ 0` and a prefactor sequence `A` with
`A_n > 0` and `log₂ A_n / n → 0`. The factor `2^{o(n)}` is `2^{g(n)}` for one `g` with `g(n)/n → 0`,
chosen after `β` and `A` and before `n`, the lattice, `λ`, `s` and `u`. Lattices are full rank,
`L = Bℤⁿ`. Volumes and the sum are in `ℝ≥0∞`. -/
theorem lemma_4_17 (β : ℝ) (hβ : 0 ≤ β) (A : ℕ → ℝ) (hA : ∀ n, 0 < A n)
    (hAo : Tendsto (fun n : ℕ => Real.logb 2 (A n) / n) atTop (nhds 0)) :
    ∃ g : ℕ → ℝ, Tendsto (fun n : ℕ => g n / n) atTop (nhds 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 →
        PointCountBound (lat B) A β → ∀ lam : ℝ, lam1 (lat B) ≤ lam →
          lam ≤ (1 + ((n : ℝ) ^ 2)⁻¹) * lam1 (lat B) → ∀ s : E n, ‖s‖ = 1 →
            ∀ u : ℝ, 3 / 16 ≤ u → u ≤ 0.4 →
              (∑' v : {v : E n // v ∈ lat B ∧ v ≠ 0},
                  volume (capShell n lam s u ∩ {x | x - (v : E n) ∈ capShell n lam s u})) /
                  volume (shellA n lam) ≤
                ENNReal.ofReal ((4 * ((2 : ℝ) ^ β) ^ 2 * (1 - u) ^ 2 / 3) ^ ((n : ℝ) / 2) *
                  (2 : ℝ) ^ g n) := by sorry

end SuperlatSVP
