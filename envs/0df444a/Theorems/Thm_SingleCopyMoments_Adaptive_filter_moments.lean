-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_filter_moments
-- name    : SingleCopyMoments.Adaptive.filter_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:47:20.239221+00:00
-- url     : https://prove2.me/theorems/25f32e49-3ce3-455c-a8c4-d522504f24ba
-- title:
--   Lemma 22 — Moments and success probability of the filter
-- statement:
--   Fix a state $\rho$ in dimension $d\ge1$, $x\in[0,1]$, $n\ge1$, $L>0$, an integer $m\ge2$, and $0<\eta<1/2$. There is a measurable pilot event of probability at least $1-48/(n\eta^2)$ on which, whenever $\|S_x\|_{op}\le L$, the filter is a contraction, its normalization trace is positive, and
--
--   $$\left|p_m(\sigma_x)-\frac{\operatorname{Tr}[(\rho+x\rho^2)^m]}{(1+xp_2(\rho))^m}\right|\le4m\eta,\qquad s_x\ge\frac{n}{4Ld}.$$
--
--   The conditional output is the actual Kraus output, not the normalized analysis matrix $B_x$. Only their spectra agree. The theorem controls the error and the probability of obtaining a successful output; it does not assume the favorable pilot event occurs.
--
--   Differences from the source:
--   - encoding: finite-dimensional states, measurable experiments, and their expectations → complex Fin d matrices, explicit Born/product measures, and normalized measurable operations; reason: the coordinate and measure conventions preserve every positive dimension and arbitrary rank; probability and integrability assertions are conclusions, not extra premises
--   - encoding: the conditional output is defined on positive success → a total normalized-state function with an explicit dummy and a positive-trace conclusion on the good event; reason: the zero-success branch is never used as a successful conditional state
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Lemma 22, (6.5), printed p. 24 (PDF p. 26); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf; PDF SHA-256 f19fd65f41a444a79243fa55aab5dfca3db6adb571b06acff78ee49932174fa9.

import Definitions.Def_SingleCopyMoments_Adaptive_Pilot

open scoped Matrix.Norms.L2Operator

open MeasureTheory
open scoped ENNReal

namespace SingleCopyMoments.Adaptive

/-- Lemma 22, printed pp.24–25 (PDF pp.26–27). -/
theorem filter_moments (d n m : ℕ) (hd : 0 < d) (hn : 1 ≤ n) (hm : 2 ≤ m)
    (H : HaarBasis d) (ρ : State d) (x L η : ℝ) (hx : x ∈ Set.Icc 0 1)
    (hL : 0 < L) (hη : η ∈ Set.Ioo 0 (1/2)) :
    ∃ E : Set (Fin n → (Fin d → ℂ)), MeasurableSet E ∧
      ENNReal.ofReal (1 - 48/((n : ℝ)*η^2)) ≤ (pilotLaw H ρ x n) E ∧
      ∀ v ∈ E, opNorm (pilotS v) ≤ L →
        Loewner ((filterK v L).conjTranspose * filterK v L) 1 ∧
        0 < (pilotS v * ρ.val).trace.re ∧
        |moment (filterState ρ v).val m -
          moment (pilotH ρ x) m / (1 + x * moment ρ.val 2)^m| ≤ 4*(m : ℝ)*η ∧
        (n : ℝ)/(4*L*d) ≤ filterSuccess ρ v L := by sorry

end SingleCopyMoments.Adaptive
