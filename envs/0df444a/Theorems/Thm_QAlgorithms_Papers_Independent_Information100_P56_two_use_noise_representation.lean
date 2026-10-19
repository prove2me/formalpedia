-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_two_use_noise_representation
-- name    : QAlgorithms.Papers.Independent.Information100.P56.two_use_noise_representation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:26:11.492783+00:00
-- url     : https://prove2.me/theorems/06072dff-c226-4c52-9861-deaa4817bd59
-- title:
--   Section VI E: criterion for two-use exchangeable repetition noise
-- statement:
--   Let $a,b,c\ge0$ with $a+2b+c=1$, so $(a,b,b,c)$ is exchangeable two-use noise. The physical/logical flip construction has
--
--   $$b=\lambda(1-\lambda),\qquad a-c=(1-2\mu)(1-2\lambda).$$
--
--   If $b\le1/4$ and $|a-c|\le\sqrt{1-4b}$, there are $\lambda,\mu\in[0,1/2]$ giving that distribution, allowing a fixed complement of the input labels. This includes $b=1/4$, when $a=c=1/4$ and $\lambda=1/2$. It does not assert representation of all exchangeable noise.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 17, Section VI E: criterion for two-use exchangeable repetition noise

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Section VI E, p.17: the two-use exchangeable-noise representation criterion.
A fixed complement is allowed. At b=1/4, a=c=1/4 and lambda=1/2 need no division. -/
theorem two_use_noise_representation (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + 2 * b + c = 1) :
    (∀ lambda mu : ℝ,
      ((1 - mu) * (1 - lambda) ^ 2 + mu * lambda ^ 2) -
        ((1 - mu) * lambda ^ 2 + mu * (1 - lambda) ^ 2) =
          (1 - 2 * mu) * (1 - 2 * lambda)) ∧
    (b ≤ 1 / 4 → |a - c| ≤ Real.sqrt (1 - 4 * b) →
      ∃ lambda ∈ Set.Icc (0 : ℝ) (1 / 2), ∃ mu ∈ Set.Icc (0 : ℝ) (1 / 2),
        ∃ flip : Bool,
          b = lambda * (1 - lambda) ∧
          (if flip then c else a) = (1 - mu) * (1 - lambda) ^ 2 + mu * lambda ^ 2 ∧
          (if flip then a else c) = (1 - mu) * lambda ^ 2 + mu * (1 - lambda) ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
