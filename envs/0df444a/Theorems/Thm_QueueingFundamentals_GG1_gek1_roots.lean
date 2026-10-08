-- Prove2me | Theorems.Thm_QueueingFundamentals_GG1_gek1_roots
-- name    : QueueingFundamentals.GG1.gek1_roots
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T19:48:43.414928+00:00
-- url     : https://prove2.me/theorems/f5e84e46-c711-41cf-a039-2392e95f26f7
-- title:
--   The G/E_k/1 characteristic roots (Chaudhry et al., 1990), §6.1, p.278
-- statement:
--   Let the interarrival distribution $A$ be a lifetime law with finite mean $\mathrm E[T]>0$, arrival rate $\lambda=1/\mathrm E[T]$ and LST $A^*$, let $\mu>0$ be the service rate of the G/E_k/1 queue (each of the $k\ge1$ exponential phases has rate $k\mu$), and assume $\lambda/\mu<1$. Consider the characteristic equation
--
--   $$
--   z^k=A^*[k\mu(1-z)]=\beta(z). \tag{6.1}
--   $$
--
--   Then:
--
--   1. exactly one root of (6.1) is real and lies in $(0,1)$;
--   2. if $k$ is even, exactly one further root is real and lies in $(-1,0)$; if $k$ is odd, no root lies in $(-1,0)$;
--   3. if $A^*(s)=[A_1^*(s)]^k$ for the LST $A_1^*$ of some lifetime law $A_1$, then (6.1) has exactly $k$ roots in the open unit disk $|z|<1$, and they are distinct: each is a simple zero of $z^k-\beta(z)$.
--
--   The roots in the unit disk determine the G/E_k/1 (equivalently G^{[k]}/M/1) arrival-point distribution, so their location and distinctness is what makes a partial-fraction solution possible.
--
--   **Formalization Note** The count "$k$ roots strictly inside the unit circle" is the setting the book gives just before the result (by Rouché's theorem, when $\lambda/\mu<1$); it is stated here together with distinctness, in the case where distinctness is asserted, so that no multiplicity count is needed. Roots are complex numbers; a real root $x$ means $x\in\mathbb R$ with $x^k=\beta(x)$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.278, §6.1, the unnumbered result of Chaudhry et al. (1990) for the characteristic equation (6.1)

import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_Lindley

namespace QueueingFundamentals.GG1

open MeasureTheory

/-- The G/E_k/1 root result of Chaudhry et al. (1990) (p.278). Let the interarrival law `A` have
finite mean `E[T] > 0`, arrival rate `λ = 1/E[T]`, service rate `μ > 0` (phase rate `kμ`), and
`λ/μ < 1`. For the characteristic equation (6.1) `z^k = A^*[kμ(1 − z)] = β(z)`:
(a) exactly one root is real and in `(0, 1)`;
(b) for even `k` exactly one further root is real and in `(−1, 0)`, and for odd `k` there is none;
(c) if `A^*(s) = [A_1^*(s)]^k` for the LST `A_1^*` of a lifetime law `A_1`, then the roots in the
open unit disk are `k` in number (the count of the setting on p.278) and pairwise distinct
(each is a simple zero of `z^k − β(z)`). -/
theorem gek1_roots (A : Measure ℝ) (hA : IsLifetimeLaw A)
    (hAint : Integrable (fun x : ℝ => x) A) (hmeanA : 0 < meanOf A)
    (mu : ℝ) (hmu : 0 < mu) (k : ℕ) (hk : 1 ≤ k)
    (hρ : (1 / meanOf A) / mu < 1) :
    (∃! x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 ∧
        (x : ℂ) ^ k = QueueingFundamentals.MG1.lst A ((k : ℂ) * mu * (1 - (x : ℂ)))) ∧
    (Even k → ∃! x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 0 ∧
        (x : ℂ) ^ k = QueueingFundamentals.MG1.lst A ((k : ℂ) * mu * (1 - (x : ℂ)))) ∧
    (¬ Even k → ∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 0 →
        (x : ℂ) ^ k ≠ QueueingFundamentals.MG1.lst A ((k : ℂ) * mu * (1 - (x : ℂ)))) ∧
    ((∃ A₁ : Measure ℝ, IsLifetimeLaw A₁ ∧ ∀ s : ℂ, 0 ≤ s.re → QueueingFundamentals.MG1.lst A s = (QueueingFundamentals.MG1.lst A₁ s) ^ k) →
      {z : ℂ | ‖z‖ < 1 ∧ z ^ k = QueueingFundamentals.MG1.lst A ((k : ℂ) * mu * (1 - z))}.ncard = k ∧
      ∀ z : ℂ, ‖z‖ < 1 → z ^ k = QueueingFundamentals.MG1.lst A ((k : ℂ) * mu * (1 - z)) →
        deriv (fun w : ℂ => w ^ k - QueueingFundamentals.MG1.lst A ((k : ℂ) * mu * (1 - w))) z ≠ 0) := by sorry

end QueueingFundamentals.GG1
