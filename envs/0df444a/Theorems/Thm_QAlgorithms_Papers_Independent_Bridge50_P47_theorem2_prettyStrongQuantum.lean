-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P47_theorem2_prettyStrongQuantum
-- name    : QAlgorithms.Papers.Independent.Bridge50.P47.theorem2_prettyStrongQuantum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:45:20.395963+00:00
-- url     : https://prove2.me/theorems/21df4006-1e7b-499f-b65e-d4597e374ce3
-- title:
--   Theorem 2: pretty strong quantum converse
-- statement:
--   Let $\mathcal N:\mathcal L(A)\to\mathcal L(B)$ be degradable, with nonzero finite dimensional input and output systems. Write $Q^{(1)}(\mathcal N)=\max_{\rho\in\mathcal S(A)}[S(\mathcal N(\rho))-S(\mathcal N^c(\rho))]$ for its maximum coherent information in bits. Let $N(n,\varepsilon)$ be the largest dimension transmitted through $n$ independent uses with worst purified distance at most $\varepsilon$, uniformly over all reference systems and joint inputs. Let $N_E(n,\varepsilon)$ instead optimize a normalized joint reference-input state and a CPTP decoder for entanglement generation. There exists a channel-dependent $\mu\ge0$, chosen before $\varepsilon$ and $n$, such that for every $0\le\varepsilon<1/\sqrt2$, with $\lambda=(1/\sqrt2-\varepsilon)/4$, and every integer $n\ge1$,
--
--   $$
--   \log_2 N(n,\varepsilon)\le\log_2 N_E(n,\varepsilon)\le nQ^{(1)}(\mathcal N)+\mu\sqrt{n\ln\frac{64n^{(\dim A)^2}}{\lambda^2}}+3(\dim A)^2\log_2 n+5+5\log_2\frac1\lambda.
--   $$
--
--   For each fixed allowed error there exist $C>0$ and $n_0\ge2$, chosen before $n$, such that the upper bound $nQ^{(1)}(\mathcal N)+C\sqrt{n\log_2 n}$ holds for all $n\ge n_0$. This is a finite-block converse with a sublinear fixed-error remainder.
-- source:
--   "Pretty strong" converse for the quantum capacity of degradable channels, arXiv:1301.4927v3, PDF p. 5, Theorem 2: pretty strong quantum converse

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

/-- Theorem 2, PDF pp.5–7: both the exact finite-block bound and its
fixed-error O(sqrt(n log n)) consequence. The channel constant precedes epsilon. -/
theorem theorem2_prettyStrongQuantum [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : P67.IsDegradable U) :
    ∃ mu : ℝ, 0 ≤ mu ∧ ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon < 1 / Real.sqrt 2 →
      let lambda := (1 / Real.sqrt 2 - epsilon) / 4
      (∀ n : ℕ, 1 ≤ n →
        logN U n epsilon ≤ logNE U n epsilon ∧
        logNE U n epsilon ≤ (n : ℝ) * P67.maximumCoherentInformation U +
          mu * Real.sqrt ((n : ℝ) * Real.log
            (64 * (n : ℝ) ^ (Fintype.card A ^ 2) / lambda ^ 2)) +
          3 * (Fintype.card A : ℝ) ^ 2 * Real.logb 2 n + 5 + 5 * Real.logb 2 (1 / lambda)) ∧
      (∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n ≥ n0,
        logNE U n epsilon ≤ (n : ℝ) * P67.maximumCoherentInformation U +
          C * Real.sqrt ((n : ℝ) * Real.logb 2 n)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P47

end
