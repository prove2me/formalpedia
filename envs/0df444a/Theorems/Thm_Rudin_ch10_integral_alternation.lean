-- Prove2me | Theorems.Thm_Rudin_ch10_integral_alternation
-- name    : Rudin.ch10_integral_alternation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T00:18:44.069766+00:00
-- url     : https://prove2.me/theorems/904225e1-68bb-4568-a061-2fab48ad007c
-- title:
--   Integrals of $k$-forms depend only on the alternation of the coefficients
-- statement:
--   Rudin presents a $k$-form in $\mathbb{R}^n$ by a family of coefficient functions
--   $a_{i_1\cdots i_k}$ indexed by *all* tuples $(i_1,\dots,i_k)$, the indices ranging independently
--   from $1$ to $n$, and defines its integral over a $k$-surface $\Phi$ with parameter domain $D$ by
--
--   $$\int_\Phi \omega = \int_D \sum_{(i_1,\dots,i_k)} a_{i_1\cdots i_k}(\Phi(u))\,\frac{\partial(\varphi_{i_1},\dots,\varphi_{i_k})}{\partial(u_1,\dots,u_k)}\,du .$$
--
--   Because a Jacobian changes sign when two of its rows are interchanged, and vanishes when an index
--   is repeated, this number depends on the coefficients only through their alternations
--
--   $$(\operatorname{Alt}a)_{i_1\cdots i_k}(x) = \sum_{\sigma\in S_k}\operatorname{sgn}(\sigma)\,a_{i_{\sigma(1)}\cdots i_{\sigma(k)}}(x).$$
--
--   The statement asserts precisely this: if two $k$-forms $\omega_1,\omega_2$ have, at every point of a
--   set $E \subseteq \mathbb{R}^n$ and for every index tuple $i$, the same alternating sum
--   $\sum_{\sigma} \operatorname{sgn}(\sigma)\,a_{i\circ\sigma}(x)$, then
--   $\int_\Phi \omega_1 = \int_\Phi \omega_2$ for every $k$-surface $\Phi$ whose parameter simplex
--   $Q^k$ is mapped into $E$. No continuity or integrability hypothesis is needed: the two integrands
--   coincide at every point of the parameter domain.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 10, Definition 10.11 (equation (35)) and Sections 10.12-10.13 (the anticommutation relations), pp. 254-256

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Chapter 10, equations (35) and (38)–(39): the integral of a `k`-form over a
`k`-surface depends on the coefficients only through their alternations.  If two `k`-forms have,
at every point of a set `E`, the same alternating sum
`∑_σ (sgn σ) a_{i∘σ}` for every index tuple `i`, then they have the same integral over every
`k`-surface whose parameter simplex is mapped into `E`. -/
theorem ch10_integral_alternation (k n : ℕ) (E : Set (Fin n → ℝ)) (ω₁ ω₂ : KForm k n)
    (halt : ∀ x ∈ E, ∀ i : Fin k → Fin n,
      ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) * ω₁.coeff (fun r => i (σ r)) x
        = ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) * ω₂.coeff (fun r => i (σ r)) x)
    (Φ : SimplexSurface k n) (hΦ : ∀ u ∈ stdSimplex k, Φ.map u ∈ E) :
    integralOverSimplex ω₁ Φ = integralOverSimplex ω₂ Φ := by sorry

end Rudin
