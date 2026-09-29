-- Prove2me | Theorems.Thm_Rudin_ch06_integral_mono_of_bounded
-- name    : Rudin.ch06_integral_mono_of_bounded
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T05:33:32.595354+00:00
-- url     : https://prove2.me/theorems/bcc7f9ca-17bf-4bc3-ae5f-75ce3dad5c33
-- title:
--   Monotonicity of the Riemann-Stieltjes integral (Rudin 6.12 b)
-- statement:
--   **Monotonicity of the Riemann–Stieltjes integral.** Let $\alpha$ be monotonically increasing on $[a,b]$ and let $f, g$ be bounded on $[a,b]$ with $f(x) \le g(x)$ for every $x \in [a,b]$. Then
--   $$\int_a^b f\,d\alpha \;\le\; \int_a^b g\,d\alpha.$$
--
--   This is part (b) of Rudin's Theorem 6.12, isolated as a standalone lemma. It is the half of that theorem that needs no refinement theory: every upper sum of $f$ is dominated term by term by the corresponding upper sum of $g$ over the *same* partition, because $\sup_I f \le \sup_I g$ on each subinterval and the increments $\Delta\alpha_i$ are nonnegative; passing to the infimum over partitions gives the claim.
--
--   **Formalization note.** Boundedness is part of Rudin's standing setup in Chapter 6 and is genuinely needed here: upper sums are built from `sSup`, which returns the junk value $0$ on sets unbounded above, and without boundedness the statement is false. On $[0,1]$ with $\alpha = \mathrm{id}$, $f(0) = -1$, $f(x) = -1/x$ for $x \neq 0$ and $g \equiv -1$, one has $f \le g$ while the two integrals come out $0$ and $-1$. Integrability of $f$ and $g$ is *not* assumed: the statement holds for the upper integral of any bounded function, which is how `Rudin.RSIntegral` is defined.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd ed., Chapter 6, Theorem 6.12(b), p. 128.

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.12(b): the Riemann-Stieltjes integral is monotone in the integrand. -/
theorem ch06_integral_mono_of_bounded (a b : ℝ) (hab : a ≤ b) (f g α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hfb : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) (hgb : ∃ M, ∀ x ∈ Set.Icc a b, |g x| ≤ M)
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    RSIntegral a b f α ≤ RSIntegral a b g α := by sorry

end Rudin
