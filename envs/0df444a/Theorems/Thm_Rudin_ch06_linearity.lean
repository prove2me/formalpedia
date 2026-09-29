-- Prove2me | Theorems.Thm_Rudin_ch06_linearity
-- name    : Rudin.ch06_linearity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T23:17:31.096723+00:00
-- url     : https://prove2.me/theorems/a5d6a672-e509-404c-a046-e131a98f90c8
-- title:
--   Theorem 6.12(a) — linearity of the integral
-- statement:
--   If $f, g \in \mathcal{R}(\alpha)$ and $c$ is a constant, then $f + g \in \mathcal{R}(\alpha)$ with $\int (f+g)\,d\alpha = \int f\,d\alpha + \int g\,d\alpha$, and $cf \in \mathcal{R}(\alpha)$ with $\int cf\,d\alpha = c\int f\,d\alpha$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 128, Theorem 6.12(a)

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.12(a): the integrable functions form a vector space and the integral is
linear on it. -/
theorem ch06_linearity (a b : ℝ) (hab : a ≤ b) (f g α : ℝ → ℝ) (c : ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hf : RSIntegrable a b f α) (hg : RSIntegrable a b g α)
    (hfb : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) (hgb : ∃ M, ∀ x ∈ Set.Icc a b, |g x| ≤ M) :
    RSIntegrable a b (fun x => f x + g x) α ∧
    RSIntegral a b (fun x => f x + g x) α = RSIntegral a b f α + RSIntegral a b g α ∧
    RSIntegrable a b (fun x => c * f x) α ∧
    RSIntegral a b (fun x => c * f x) α = c * RSIntegral a b f α := by sorry

end Rudin
