-- Prove2me | Theorems.Thm_Rudin_ch06_integral_mono_of_bounded_larger
-- name    : Rudin.ch06_integral_mono_of_bounded_larger
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-18T15:06:20.575619+00:00
-- url     : https://prove2.me/theorems/986a5528-4afe-4373-85a2-40d3f8635ea0
-- title:
--   Theorem 6.12(b) with boundedness assumed only for the larger integrand
-- statement:
--   Rudin's Theorem 6.12(b) states that if $f, g \in \mathcal R(\alpha)$ on $[a,b]$ and $f \le g$ there, then $\int_a^b f\,d\alpha \le \int_a^b g\,d\alpha$. In this development, where upper and lower integrals are ordinary suprema and infima of sets of reals and therefore take a default value on unbounded sets, Rudin's standing hypothesis of Definition 6.2 — that the integrands be bounded — has to be stated explicitly; the proved form `Rudin.ch06_integral_mono_of_bounded` assumes it for **both** $f$ and $g$.
--
--   This statement asks whether one of the two hypotheses can be dropped: it assumes
--
--   $$\alpha \text{ monotonically increasing},\qquad f, g \in \mathcal R(\alpha) \text{ on } [a,b], \qquad f \le g \text{ on } [a,b],$$
--
--   together with boundedness of the **larger** integrand $g$ only, and asserts
--
--   $$\int_a^b f\,d\alpha \le \int_a^b g\,d\alpha .$$
--
--   It is the natural first attempt at a minimal hypothesis, since a function below a bounded function is bounded above, and it is recorded here so that the sharpness of the hypotheses in 6.12(b) is settled on the record rather than assumed.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 128, Theorem 6.12(b) (hypothesis-sharpness variant: boundedness assumed only for the larger integrand)

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.12(b), with the boundedness hypothesis imposed only on the larger integrand
`g`: if `f ≤ g` on `[a, b]`, both are integrable and `g` is bounded, is the integral monotone? -/
theorem ch06_integral_mono_of_bounded_larger (a b : ℝ) (hab : a ≤ b) (f g α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hgb : ∃ M, ∀ x ∈ Set.Icc a b, |g x| ≤ M)
    (hf : RSIntegrable a b f α) (hg : RSIntegrable a b g α)
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    RSIntegral a b f α ≤ RSIntegral a b g α := by sorry

end Rudin
