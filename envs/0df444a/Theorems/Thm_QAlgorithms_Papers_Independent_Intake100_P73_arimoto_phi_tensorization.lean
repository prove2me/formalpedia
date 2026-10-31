-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P73_arimoto_phi_tensorization
-- name    : QAlgorithms.Papers.Independent.Intake100.P73.arimoto_phi_tensorization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:59:11.639508+00:00
-- url     : https://prove2.me/theorems/5bf0b0d3-c22c-4d64-8704-3c8e2189b01a
-- title:
--   Arimoto: optimized phi-moment tensorization, (43)
-- statement:
--   For a normalized discrete channel W with nonempty input alphabet, positive integer n, and -1<t<=0, the supremum over all block input laws on X^n of exp(phi(t|W^n,p)) equals the nth power of the supremum over single-letter input laws of exp(phi(t|W,p)). Block laws are unrestricted. Extrema denote numerical suprema without optimizer witnesses. Hayashi explicitly attributes (43) to Arimoto [15].
-- source:
--   General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel, arXiv:cs/0503088v2, PDF p. 10, Lemma 7 (43), attributed to Arimoto [15]

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P73

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P73

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

/-- Hayashi PDF pp.10–11, Lemma 7 (43), explicitly attributed to Arimoto [15].
Block input laws are arbitrary, not required to be iid. Printed maxima are
changed to numerical suprema: arbitrary row sets need not attain an optimizer.
The source optimal values are retained without optimizer-attainment claims. -/
theorem arimoto_phi_tensorization {X Y : Type*} [Nonempty X]
    (W : X → Y → ℝ≥0∞) (hW : IsDiscreteStochastic W)
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : -1 < t) (ht0 : t ≤ 0) :
    (⨆ p : PMF (Fin n → X), phiMoment (memorylessKernel W n) p t) =
      (⨆ p : PMF X, phiMoment W p t) ^ n := by sorry

end QAlgorithms.Papers.Independent.Intake100.P73

end
