-- Prove2me | Theorems.Thm_ThinShellSampling_lemma_5_2
-- name    : ThinShellSampling.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:16.629849+00:00
-- url     : https://prove2.me/theorems/2fc13523-33c3-4d4f-9fa2-c2952d33c3ef
-- title:
--   Lemma 5.2 — Rényi closeness of Gaussian tilts
-- statement:
--   Let $\nu$ be any probability measure on $\mathbb R^n$ and $\nu_s(dx)\propto e^{-s\|x\|^2}\nu(dx)$ for $s\ge0$. For $q>1$ and $s\ge s'\ge0$,
--
--   $$
--   \mathsf R_q(\nu_s\,\|\,\nu_{s'})\le\frac q2\,(s-s')^2\sup_{t\in[s',\,qs-(q-1)s']}\operatorname{Var}_{\nu_t}(\|X\|^2).
--   $$
--
--   No logconcavity is needed. Combined with a thin-shell bound on the variance, the lemma says how far apart consecutive annealing targets may be.
--
--   **Formalization Note** The right-hand side is in $[0,\infty]$ with $0\cdot\infty=0$ (at $s=s'$ both sides are $0$).
--
--   Differences from the source:
--
--   - encoding: sup of real variances → supremum of evariance in [0, ∞], multiplied in [0, ∞]; reason: Lean convention; same value on every instance with finite variances, and the bound is trivial otherwise
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Lemma 5.2, eq. (5.1), p.31 (PDF p.33)

import Mathlib
import Definitions.Def_ThinShellSampling_renyi
import Definitions.Def_ThinShellSampling_expTilt

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Lemma 5.2 (Rényi closeness of Gaussian tilts).**

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), §5.2, p.31 (PDF p.33): "For a probability measure `ν`, let `ν_s(dx) ∝ e^{−s‖x‖²} ν(dx)` for
`s ≥ 0`." Lemma 5.2: "Let `q > 1` and `s ≥ s′ ≥ 0`. Then,
`R_q(ν_s ‖ ν_{s′}) ≤ q/2 (s − s′)² sup_{t∈[s′, qs−(q−1)s′]} Var_{ν_t}(‖X‖²)`. (5.1)" "This result does not
require logconcavity of `ν`."

**Formalization Note.** `ν` is any probability measure on `ℝⁿ`. The right-hand side is computed in
`[0, ∞]` (`evariance`), with `0 · ∞ = 0` at `s = s′`, where both sides are `0`. -/
theorem lemma_5_2 (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (q s s' : ℝ) (hq : 1 < q) (hs' : 0 ≤ s') (hss : s' ≤ s) :
    renyi q (expTilt ν (fun x => s * ‖x‖ ^ 2)) (expTilt ν (fun x => s' * ‖x‖ ^ 2)) ≤
      ENNReal.ofReal (q / 2 * (s - s') ^ 2) *
        ⨆ t ∈ Set.Icc s' (q * s - (q - 1) * s'),
          evariance (fun x => ‖x‖ ^ 2) (expTilt ν (fun x => t * ‖x‖ ^ 2)) := by sorry

end ThinShellSampling
