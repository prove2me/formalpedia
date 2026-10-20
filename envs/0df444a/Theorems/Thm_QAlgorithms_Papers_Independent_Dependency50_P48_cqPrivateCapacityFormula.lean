-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P48_cqPrivateCapacityFormula
-- name    : QAlgorithms.Papers.Independent.Dependency50.P48.cqPrivateCapacityFormula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:37:59.736597+00:00
-- url     : https://prove2.me/theorems/ab46afb7-1bb8-4901-9a53-fe53edf2eee8
-- title:
--   Regularized private and key capacities of a cq wiretap channel
-- statement:
--   Let $W:x\mapsto\rho_x^{QE}$ be a memoryless classical–quantum wiretap channel with a finite nonempty input alphabet and finite nonempty receiver and eavesdropper registers. Every output is a positive semidefinite density matrix of trace one; it need not be pure or a product. Let $C_p(W)$ and $K(W)$ be the operational private-message and uniform-secret-key capacities with free forward public communication. Their codes have independent private randomness for a prescribed uniform message, or a uniform key that is a function of Alice's randomness, respectively. Reliability and the two secrecy constraints are $\Pr(K
--   e L)\le\epsilon$, $I(K;S)\le\epsilon$, and $I(K;E^n\mid S)\le\epsilon$, separately. There is no initial shared key or entanglement and no backward channel.
--
--   For each positive integer $l$, maximize over every finite joint law of an auxiliary variable $T$ and an input word $X^l$, with output conditioned on $(T,X^l)$ equal to $W^{\otimes l}(X^l)$. These maxima are attained, and
--
--   $$C_p(W)=K(W)=\lim_{l\to\infty}\frac1l\max_{T\to X^l\to Q^lE^l}\{I(T;Q^l)-I(T;E^l)\}.$$
--
--   All entropies are in bits and rates are per channel use. Achievability requires codes of rate at least $R-\delta$ for every positive error and slack and every sufficiently large positive blocklength. This result retains stochastic preprocessing through $T$.
-- source:
--   The private classical capacity and quantum capacity of a quantum channel, arXiv:quant-ph/0304127v6, PDF p. 4, Theorem 1 / (6)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P48

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P67 (dilationPower)

attribute [local instance] Classical.propDecidable

variable {P Q E X H : Type*}

variable [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

variable [Fintype E] [DecidableEq E] [Fintype X] [DecidableEq X]

variable [Fintype H] [DecidableEq H]

/-- Theorem 1, (6), PDF p.4 (model pp.3–4, proof pp.4–8): regularized private
and key capacities of a cq wiretap channel, optimizing over all finite T.
The maximum is attained; an optimizing law is not an assumed hypothesis. -/
theorem cqPrivateCapacityFormula [Nonempty X] [Nonempty Q] [Nonempty E]
    (W : X → Matrix (Q × E) (Q × E) ℂ) (hW : ∀ x, IsDensityMatrix (W x)) :
    cqCapacity W .message true = cqCapacity W .key true ∧
    Tendsto (cqRate W) atTop (nhds (cqCapacity W .message true)) ∧
    (∀ n : ℕ, 0 < n → ∃ law : MarkovLaw (Fin n → X),
      cqAdvantage (cqPower W n) law = cqMaximum (cqPower W n)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P48

end
