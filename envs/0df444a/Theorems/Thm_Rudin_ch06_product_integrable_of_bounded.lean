-- Prove2me | Theorems.Thm_Rudin_ch06_product_integrable_of_bounded
-- name    : Rudin.ch06_product_integrable_of_bounded
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T13:20:25.905546+00:00
-- url     : https://prove2.me/theorems/0a74bddc-f30e-4ba8-98f3-ae83f5747e37
-- title:
--   Theorem 6.13(a) — the product of two integrable functions is integrable
-- statement:
--   Let $\\alpha$ be monotonically increasing on $[a,b]$ and let $f$ and $g$ be bounded real functions on $[a,b]$, each integrable with respect to $\\alpha$. Then their pointwise product is integrable with respect to $\\alpha$:
--
--   $$f \\in \\mathcal{R}(\\alpha), \\quad g \\in \\mathcal{R}(\\alpha) \\;\\Longrightarrow\\; fg \\in \\mathcal{R}(\\alpha) \\text{ on } [a,b].$$
--
--   Only integrability of the product is asserted; no formula for $\\int_a^b fg\\,d\\alpha$ is claimed, and indeed none exists in general.
--
--   This closure property is what makes $\\mathcal{R}(\\alpha)$ an algebra rather than merely a vector space, and it is the step that licenses integration by parts and the treatment of Fourier coefficients: both require knowing that a product of integrable factors may itself be integrated.
--
--   **Formalization Note** Rudin's Definition 6.2 assumes throughout that integrands are bounded on the interval of integration, and those hypotheses appear explicitly here as `hfb` and `hgb`, since the formalized upper and lower integrals are ordinary suprema and infima of sets of real numbers, which take a default value on unbounded sets.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, pp. 129-130, Theorem 6.13(a) (with the boundedness hypotheses of Definition 6.2)

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.13(a), with the boundedness hypotheses of Chapter 6: if `f` and `g` are
bounded on `[a, b]` and both integrable with respect to a monotonically increasing `α`, then so
is their product `f g`. -/
theorem ch06_product_integrable_of_bounded (a b : ℝ) (hab : a ≤ b) (f g α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hf : RSIntegrable a b f α) (hg : RSIntegrable a b g α)
    (hfb : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) (hgb : ∃ M, ∀ x ∈ Set.Icc a b, |g x| ≤ M) :
    RSIntegrable a b (fun x => f x * g x) α := by sorry

end Rudin
