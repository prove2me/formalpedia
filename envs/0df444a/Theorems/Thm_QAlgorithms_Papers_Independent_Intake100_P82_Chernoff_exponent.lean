-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_Chernoff_exponent
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.Chernoff_exponent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:10:50.348256+00:00
-- url     : https://prove2.me/theorems/c544d319-e550-4058-b0ec-37427b46b317
-- title:
--   Proposition 1.6: Chernoff exponent
-- statement:
--   For each positive integer $n$, let $(\Omega_n,\mathcal F_n,P_n)$ be an arbitrary probability space and let $\Theta_n$ be a measurable involution. Assume $\widehat P_n=(\Theta_n)_*P_n$ and $P_n$ are mutually absolutely continuous. Write $\sigma_n=\log(dP_n/d\widehat P_n)$ for a real almost-everywhere representative. No finite moment assumption is imposed.
--
--   Assume $\sigma_n/n$ satisfies the full speed-$n$ LDP with convex rate $I$. Define $\|P-Q\|_{\rm var}=\sup_{A\text{ measurable}}|P(A)-Q(A)|$ and let $\underline c,\overline c$ be the liminf and limsup of the normalized logarithm below. Then
--   $$\underline c=\overline c=\lim_{n\to\infty}\frac1n\log(1-\|P_n-\widehat P_n\|_{\rm var})=-I(0).$$
--   The variation normalization is at most one for probabilities. This identifies both Chernoff exponents and asserts existence of the actual extended limit.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 16, Proposition 1.6: Chernoff exponent

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P82

noncomputable section

open Filter MeasureTheory Set

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P82

attribute [local instance] Classical.propDecidable

/-- Proposition 1.6, arXiv:1712.05167v3, PDF p.16. Lower exponent, upper
exponent and actual limit all coincide with -I(0); variation uses sup-event,
not the unhalved L1 convention. -/
theorem Chernoff_exponent (O : ℕ → Type*) [∀ n, MeasurableSpace (O n)]
    (D : (n : ℕ) → ReversalExperiment (O n)) (I : ℝ → EReal)
    (hft : FullLDP (fun n A => (D n).law {x | experimentLogDensity (D n) x / (n : ℝ) ∈ A}) I)
    (hconv : ExtendedRateConvex I) :
    liminf (fun n : ℕ => chernoffTerm (D (n + 1)) (n + 1)) atTop = -I 0 ∧
    limsup (fun n : ℕ => chernoffTerm (D (n + 1)) (n + 1)) atTop = -I 0 ∧
    Tendsto (fun n : ℕ => chernoffTerm (D (n + 1)) (n + 1)) atTop (𝓝 (-I 0)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P82

end
