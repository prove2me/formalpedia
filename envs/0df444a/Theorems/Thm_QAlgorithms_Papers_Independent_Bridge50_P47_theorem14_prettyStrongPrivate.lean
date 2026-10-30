-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P47_theorem14_prettyStrongPrivate
-- name    : QAlgorithms.Papers.Independent.Bridge50.P47.theorem14_prettyStrongPrivate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:48:22.947694+00:00
-- url     : https://prove2.me/theorems/d9970031-e4da-4425-b64a-3baaed1b64a4
-- title:
--   Theorem 14: pretty strong private converse
-- statement:
--   Let $\mathcal N:\mathcal L(A)\to\mathcal L(B)$ be degradable on nonzero finite quantum systems. Let $M(n,\varepsilon,\delta)$ be the largest number of uniform messages encoded into possibly mixed states for $n$ independent uses and decoded by a POVM. Error is the purified distance between the decoded $X\widehat X$ marginal and the uniform perfectly correlated state. Privacy is the minimum purified distance between the $XE$ marginal and the uniform message tensor a normalized environment state. Write $Q^{(1)}(\mathcal N)$ for the maximum coherent information in bits. There exists a channel-dependent $\mu\ge0$, independent of both tolerances and $n$, such that for $\varepsilon,\delta\ge0$ with $\varepsilon+2\delta<1/\sqrt2$, and $\eta=(1/\sqrt2-\varepsilon-2\delta)/6$, every integer $n\ge1$ satisfies
--
--   $$
--   \log_2 M(n,\varepsilon,\delta)\le nQ^{(1)}(\mathcal N)+\mu\sqrt{n\ln\frac{64n^{(\dim A)^2}}{\eta^2}}+3(\dim A)^2\log_2 n+9+11\log_2\frac1\eta.
--   $$
--
--   For each fixed allowed pair there are $C>0,n_0\ge2$, chosen before $n$, giving the upper bound $nQ^{(1)}(\mathcal N)+C\sqrt{n\log_2 n}$ for all $n\ge n_0$. This is a converse for the separate marginal error and privacy criteria.
-- source:
--   "Pretty strong" converse for the quantum capacity of degradable channels, arXiv:1301.4927v3, PDF p. 9, Theorem 14: pretty strong private converse

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P47

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Bridge50.P47

open QAlgorithms.Papers.Independent.Information100

variable {A B E F R I O : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

variable [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]

variable [Fintype O] [DecidableEq O]

/-- Theorem 14, PDF pp.9–10: separate purified error and privacy, with the
channel constant independent of both tolerances and of blocklength. -/
theorem theorem14_prettyStrongPrivate [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : P67.IsDegradable U) :
    ∃ mu : ℝ, 0 ≤ mu ∧ ∀ epsilon delta : ℝ, 0 ≤ epsilon → 0 ≤ delta →
      epsilon + 2 * delta < 1 / Real.sqrt 2 →
      let eta := (1 / Real.sqrt 2 - epsilon - 2 * delta) / 6
      (∀ n : ℕ, 1 ≤ n →
        logM U n epsilon delta ≤ (n : ℝ) * P67.maximumCoherentInformation U +
          mu * Real.sqrt ((n : ℝ) * Real.log
            (64 * (n : ℝ) ^ (Fintype.card A ^ 2) / eta ^ 2)) +
          3 * (Fintype.card A : ℝ) ^ 2 * Real.logb 2 n + 9 + 11 * Real.logb 2 (1 / eta)) ∧
      (∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n ≥ n0,
        logM U n epsilon delta ≤ (n : ℝ) * P67.maximumCoherentInformation U +
          C * Real.sqrt ((n : ℝ) * Real.logb 2 n)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P47

end
