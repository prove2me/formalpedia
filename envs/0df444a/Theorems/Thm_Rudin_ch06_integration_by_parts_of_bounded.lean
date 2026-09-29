-- Prove2me | Theorems.Thm_Rudin_ch06_integration_by_parts_of_bounded
-- name    : Rudin.ch06_integration_by_parts_of_bounded
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T13:20:32.779311+00:00
-- url     : https://prove2.me/theorems/a9ee2469-3026-4de3-90ff-6681b4636bf5
-- title:
--   Theorem 6.22 — integration by parts (bounded integrands)
-- statement:
--   This is integration by parts, in the form Rudin states it, with the boundedness hypotheses that Definition 6.1 places on members of $\\mathcal{R}$.
--
--   Let $F$ and $G$ be differentiable at every point of $[a,b]$, with derivatives $F' = f$ and $G' = g$, and suppose $f$ and $g$ are bounded on $[a,b]$ and Riemann integrable there. Then
--
--   $$\\int_a^b F(x)\\,g(x)\\,dx \\;=\\; F(b)G(b) - F(a)G(a) - \\int_a^b f(x)\\,G(x)\\,dx .$$
--
--   Both integrals exist: $F$ and $G$ are continuous, hence integrable, and products of bounded integrable functions are integrable.
--
--   Integration by parts is the integral counterpart of the product rule for derivatives, and it is the standard device for transferring a derivative from one factor to the other — the basic tool behind the asymptotic estimates of Chapter 8 and behind the theory of Fourier series.
--
--   **Formalization Note** The boundedness hypotheses `hfb` and `hgb` carry the clause of Rudin's Definition 6.1 that a member of $\\mathcal{R}$ is bounded; the formalized upper and lower integrals are ordinary suprema and infima of sets of real numbers, which take a default value on unbounded sets. Differentiability on the closed interval is expressed as a two-sided derivative at every point of $[a,b]$, as in Rudin's statement.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 134, Theorem 6.22 (with the boundedness hypotheses of Definitions 6.1-6.2)

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.22 (integration by parts), with the boundedness hypotheses of Chapter 6:
if `F` and `G` are differentiable on `[a, b]` with `F' = f ∈ ℛ` and `G' = g ∈ ℛ`, both `f` and
`g` bounded, then `∫ₐᵇ F g dx = F b G b - F a G a - ∫ₐᵇ f G dx`. -/
theorem ch06_integration_by_parts_of_bounded (a b : ℝ) (hab : a ≤ b) (F G f g : ℝ → ℝ)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x)
    (hG : ∀ x ∈ Set.Icc a b, HasDerivAt G (g x) x)
    (hf : RiemannIntegrable a b f) (hg : RiemannIntegrable a b g)
    (hfb : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) (hgb : ∃ M, ∀ x ∈ Set.Icc a b, |g x| ≤ M) :
    RiemannIntegral a b (fun x => F x * g x) =
      F b * G b - F a * G a - RiemannIntegral a b (fun x => f x * G x) := by sorry

end Rudin
