-- Prove2me | Theorems.Thm_Rudin_ch06_fundamental_theorem_of_bounded
-- name    : Rudin.ch06_fundamental_theorem_of_bounded
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T13:13:11.762016+00:00
-- url     : https://prove2.me/theorems/fc5a3bdf-8753-479d-ac41-89b98351d3f5
-- title:
--   Theorem 6.21 — the fundamental theorem of calculus (bounded integrand)
-- statement:
--   This is the fundamental theorem of calculus in the form Rudin states it, with the boundedness hypothesis that his Definition 6.1 places on a Riemann integrable function made explicit.
--
--   Let $f$ be a bounded real function on $[a,b]$ which is Riemann integrable there, $f \\in \\mathcal{R}$, and suppose there is a function $F$ on $[a,b]$ which is differentiable at every point of $[a,b]$ with $F'(x) = f(x)$. Then
--
--   $$\\int_a^b f(x)\\,dx = F(b) - F(a).$$
--
--   No continuity of $f$ is assumed: integrability of $f$ together with the existence of an antiderivative suffices. Here $\\int_a^b f\\,dx$ is the Riemann integral in the sense of Rudin's Definition 6.2 with the integrator $\\alpha(x) = x$, i.e. the common value of $\\inf_P U(P,f)$ and $\\sup_P L(P,f)$ over all partitions $P$ of $[a,b]$.
--
--   The theorem is what makes integrals computable: it reduces integration to antidifferentiation and is the link between the differentiation theory of Chapter 5 and the integration theory of Chapter 6.
--
--   **Formalization Note** Rudin's class $\\mathcal{R}$ consists of *bounded* functions whose upper and lower integrals agree; the boundedness clause is carried here by the explicit hypothesis `hfb`, since the formalized upper and lower integrals are ordinary suprema and infima of sets of real numbers, which take a default value on unbounded sets. Differentiability on the closed interval is expressed as a two-sided derivative at every point of $[a,b]$, as in Rudin's statement.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 134, Theorem 6.21 (with the boundedness hypothesis of Definitions 6.1-6.2)

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.21 (the fundamental theorem of calculus), with the boundedness hypothesis
of Chapter 6: if `f ∈ ℛ` on `[a, b]`, `f` is bounded on `[a, b]`, and `F` is differentiable on
`[a, b]` with `F' = f`, then `∫ₐᵇ f dx = F b - F a`. -/
theorem ch06_fundamental_theorem_of_bounded (a b : ℝ) (hab : a ≤ b) (f F : ℝ → ℝ)
    (hf : RiemannIntegrable a b f)
    (hfb : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x) :
    RiemannIntegral a b f = F b - F a := by sorry

end Rudin
