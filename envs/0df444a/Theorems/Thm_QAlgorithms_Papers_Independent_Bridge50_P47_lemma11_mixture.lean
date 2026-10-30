-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P47_lemma11_mixture
-- name    : QAlgorithms.Papers.Independent.Bridge50.P47.lemma11_mixture
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:47:34.067687+00:00
-- url     : https://prove2.me/theorems/35b6fdc1-4851-481a-b061-b763ea0b39b1
-- title:
--   Lemma 11: smooth max-entropy of an ensemble mixture
-- statement:
--   Let $A,B$ be nonzero finite quantum systems and $M\ge1$. Let $\rho_i$ be normalized density operators on $A\otimes B$, and let $p_i\ge0$ sum to one. Put $\bar\rho=\sum_{i=1}^M p_i\rho_i$. For every $0\le\varepsilon\le1$,
--
--   $$
--   H_{\max}^{\varepsilon}(A|B)_{\bar\rho}\le\max_{1\le i\le M}H_{\max}^{\varepsilon}(A|B)_{\rho_i}+\log_2 M.
--   $$
--
--   The same purified-distance smoothing is used in every term, over subnormalized positive operators. Values lie in the extended reals, including $-\infty$ when the zero operator is feasible. This bounds the entropy overhead of forming a normalized finite ensemble mixture.
-- source:
--   "Pretty strong" converse for the quantum capacity of degradable channels, arXiv:1301.4927v3, PDF p. 7, Lemma 11: smooth max-entropy of an ensemble mixture

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

/-- Lemma 11, PDF p.7 and appendix p.15: finite normalized ensemble,
including zero weights and epsilon=1. Extended entropy preserves log-zero=-infinity. -/
theorem lemma11_mixture [Nonempty A] [Nonempty B]
    (M : ℕ) (hM : 0 < M) (p : Fin M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (rho : Fin M → Matrix (A × B) (A × B) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1) :
    P67.smoothConditionalMaxEntropyExtended (∑ i, (p i : ℂ) • rho i) epsilon ≤
      (⨆ i : Fin M, P67.smoothConditionalMaxEntropyExtended (rho i) epsilon) +
        (Real.logb 2 M : EReal) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P47

end
