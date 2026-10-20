-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_lemma6
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.lemma6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:28:29.322384+00:00
-- url     : https://prove2.me/theorems/6583ed1c-a50c-4c8d-977e-9f9b9bff83db
-- title:
--   Conditionally typical subsets with quantum entropy control
-- statement:
--   Fix a finite cq ensemble $E=\{p(x),\rho_x^Q\}$ and a stochastic auxiliary $U\to X\to Q$. All systems are nonempty and all entropies are in bits. For every $\epsilon,\delta>0$ there are positive thresholds $N_1\le N_2$, chosen before the blocklength and event, as follows. For every $n\ge N_1$ and event $\mathcal E\subseteq\mathcal X^n$ of probability at least $\epsilon$, there exist a positive-probability subset $\mathcal F\subseteq\mathcal E$ and a $\delta$-typical word $u^n$ such that
--
--   $$\mathcal F\subseteq T^n_{X|U,\delta}(u^n),\qquad\left|\frac1n\log_2|\mathcal F|-H(X|U)\right|\le\delta.$$
--
--   For every $n\ge N_2$ and such event there is a joint witness satisfying these conclusions and
--
--   $$\frac1n H(Q^n\mid X^n\in\mathcal F)\le H(Q|U)+\delta.$$
--
--   Typicality uses the source’s absolute frequency deviations with tolerance $n\delta$; the quantum state is the normalized conditional iid state on the event. This lemma supplies the entropy-controlled subsets needed for deterministic coarse graining.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 10, Lemma 6: a large conditionally typical subset with quantum entropy control

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

section CQStatements

variable {X Q Y T : Type} [Fintype X] [Fintype Q] [Fintype Y] [Fintype T]
  [DecidableEq X] [DecidableEq Q] [DecidableEq Y] [DecidableEq T]
  [Nonempty X] [Nonempty Q] [Nonempty Y] [Nonempty T]

/-- PDF p.10, Lemma 6: thresholds precede the word event; the larger threshold yields a joint
classical and quantum witness. Absolute-value bars in (14) were verified in the PDF image. -/
theorem lemma6 (E : CQData X Q) (hE : E.Valid) (V : Auxiliary X)
    (epsilon delta : ℝ) (he : 0 < epsilon) (hd : 0 < delta) :
    ∃ N1 N2 : ℕ, 0 < N1 ∧ N1 ≤ N2 ∧
    (∀ n : ℕ, N1 ≤ n → ∀ Eset : Finset (Fin n → X), epsilon ≤ eventMass E n Eset →
      ∃ F : Finset (Fin n → X), ∃ u : Fin n → Fin V.size, GoodSubset E V n delta Eset F u) ∧
    (∀ n : ℕ, N2 ≤ n → ∀ Eset : Finset (Fin n → X), epsilon ≤ eventMass E n Eset →
      ∃ F : Finset (Fin n → X), ∃ u : Fin n → Fin V.size,
        GoodSubset E V n delta Eset F u ∧
        vnEntropy (eventState E n F) / n ≤ quantumGivenAux E V + delta) := by sorry

end CQStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
