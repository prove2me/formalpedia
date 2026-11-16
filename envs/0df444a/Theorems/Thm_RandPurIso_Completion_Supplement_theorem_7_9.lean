-- Prove2me | Theorems.Thm_RandPurIso_Completion_Supplement_theorem_7_9
-- name    : RandPurIso.Completion.Supplement.theorem_7_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:56:18.750204+00:00
-- url     : https://prove2.me/theorems/557272a7-4dd2-4847-aaeb-9fb67c3e7e71
-- title:
--   Theorem 7.9 — $\mathrm{TD}(\rho_{\mathsf{SAME}},\rho_{\mathsf{DIFF}})\le 8q^{3/2}/\sqrt L$ for $q$ forward channel queries
-- statement:
--   Let $L\ge1$ and $d\ge2$, and let $\mathsf{SAME}$, $\mathsf{DIFF}$ be the channels of Definition 7.6 built from hidden pairs that are the first two columns of $L$ independent Haar-random unitaries on $\mathbb C^d$. Let $\mathcal A$ make at most $q\ge1$ forward queries to the unknown channel, and let $\rho_{\mathsf{SAME}}$, $\rho_{\mathsf{DIFF}}$ be its final states in the two experiments, averaged over the choice of the hidden pairs (sampled once per experiment). Then
--
--   $$
--   \mathrm{TD}(\rho_{\mathsf{SAME}},\rho_{\mathsf{DIFF}})\le\frac{8q^{3/2}}{\sqrt L}.
--   $$
--
--   Consequently, if $\mathrm{TD}(\rho_{\mathsf{SAME}},\rho_{\mathsf{DIFF}})\ge\delta>0$ then $q\ge(\delta/8)^{2/3}L^{1/3}$: a constant distinguishing advantage requires $\Omega(L^{1/3})$ queries.
--
--   This is the quantitative core of Theorem 7.1 (take $d=2$, $L=\lfloor(D-1)/2\rfloor$) and of the search lower bound, Theorem 7.10.
--
--   **Formalization Note** $\mathcal A$ is the base mission's `OracleAlg` (any finite workspace, any initial density matrix, arbitrary CPTP steps); a forward query is `chanOracle`. The averages are Bochner integrals over the hidden pairs of the final state, taken outside the run.
--
--   Differences from the source:
--   - encoding: A makes at most q forward queries; final states averaged over the hidden pairs, sampled once and fixed throughout each experiment → OracleAlg with numQueries ≤ q against chanOracle; ∫ A.run(chanOracle (hiddenChannel b U)) d(hiddenPairMeasure L d), the integral outside the run; reason: the base mission's algorithm model; same instances
--   - reading: Consequently, achieving a constant distinguishing advantage requires Ω(L^{1/3}) queries → TD ≥ δ > 0 implies q ≥ (δ/8)^{2/3} L^{1/3}; reason: the consequence stated with the theorem's own constant 8
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem 7.9, p. 51 (construction pp. 49–50)

import Mathlib
import Definitions.Def_RandPurIso_Completion_OracleAlg
import Definitions.Def_RandPurIso_Completion_traceDist
import Definitions.Def_RandPurIso_Completion_Supplement_chanOracle
import Definitions.Def_RandPurIso_Completion_Supplement_hiddenDilation
import Definitions.Def_RandPurIso_Completion_Supplement_hiddenPairMeasure
open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace RandPurIso.Completion.Supplement

open RandPurIso.Completion

/-- **Theorem 7.9** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §7.2, p. 51).

Let `L ≥ 1`, `d ≥ 2`, and let `A` make at most `q ≥ 1` forward queries to the unknown channel (SAME or
DIFF of Definition 7.6). Let `ρ_SAME` and `ρ_DIFF` be its final states in the two experiments,
averaged over the choice of the hidden pairs. Then `TD(ρ_SAME, ρ_DIFF) ≤ 8 q^{3/2} / √L`.
Consequently, achieving a constant distinguishing advantage requires `Ω(L^{1/3})` queries.

**Formalization Note.**
* `A` is any oracle algorithm of the base mission (`OracleAlg`: arbitrary CPTP steps, any finite
  workspace, any initial density matrix) with query register `In`; a forward query is the stateless
  channel oracle `chanOracle`.
* The hidden pairs are sampled once per experiment: the expectation (Bochner integral against
  `hiddenPairMeasure L d`, `L` independent Haar unitaries on `ℂ^d`) is taken of the final state
  `A.run`, outside the run. The integrand is continuous on a compact group.
* The "Consequently" sentence is stated with the same constant: a trace distance `≥ δ > 0` forces
  `q ≥ (δ/8)^{2/3} L^{1/3}`. -/
theorem theorem_7_9 :
    ∀ L d : ℕ, 1 ≤ L → 2 ≤ d → ∀ q : ℕ, 1 ≤ q →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (A : OracleAlg (InSp L d) (InSp L d) W),
        A.numQueries ≤ q →
        traceDist (∫ U, A.run (chanOracle (hiddenChannel false U)) ∂(hiddenPairMeasure L d))
            (∫ U, A.run (chanOracle (hiddenChannel true U)) ∂(hiddenPairMeasure L d)) ≤
          8 * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt L ∧
        ∀ δ : ℝ, 0 < δ →
          δ ≤ traceDist (∫ U, A.run (chanOracle (hiddenChannel false U)) ∂(hiddenPairMeasure L d))
            (∫ U, A.run (chanOracle (hiddenChannel true U)) ∂(hiddenPairMeasure L d)) →
          (δ / 8) ^ ((2 : ℝ) / 3) * (L : ℝ) ^ ((1 : ℝ) / 3) ≤ q := by sorry

end RandPurIso.Completion.Supplement
