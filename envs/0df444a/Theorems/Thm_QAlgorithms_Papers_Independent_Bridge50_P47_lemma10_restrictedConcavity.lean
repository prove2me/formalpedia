-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P47_lemma10_restrictedConcavity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P47.lemma10_restrictedConcavity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:46:54.27638+00:00
-- url     : https://prove2.me/theorems/c6e08ac5-162d-4d3a-a773-66fc13b15e53
-- title:
--   Lemma 10: restricted concavity of smooth max-entropy
-- statement:
--   Let $A,B$ be nonzero finite quantum systems, let $\rho$ be a normalized density operator on $A\otimes B$, and let $M\ge1$. Let $p_i\ge0$, $\sum_{i=1}^M p_i=1$, and let $U_i,V_i$ be unitaries on $A,B$, respectively. Put $\rho_i=(U_i\otimes V_i)\rho(U_i\otimes V_i)^\dagger$ and $\bar\rho=\sum_i p_i\rho_i$. For every $\varepsilon\ge0$,
--
--   $$
--   H_{\max}^{\varepsilon}(A|B)_{\bar\rho}\ge H_{\max}^{\varepsilon\sqrt2}(A|B)_\rho.
--   $$
--
--   Smoothing optimizes over positive operators of trace at most one within purified distance $\varepsilon$, using generalized root fidelity with its missing-mass term. Entropy is extended real, with $H_{\max}(0)=-\infty$. This gives the restricted concavity needed for mixtures of locally unitary conjugates.
-- source:
--   "Pretty strong" converse for the quantum capacity of degradable channels, arXiv:1301.4927v3, PDF p. 7, Lemma 10: restricted concavity of smooth max-entropy

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

/-- Lemma 10, PDF p.7 and appendix pp.14–15: the bar is on the mixture
on the left, and the right smoothing is epsilon times sqrt(2).
The final A|C labels in the appendix are typographical slips for A|B. -/
theorem lemma10_restrictedConcavity [Nonempty A] [Nonempty B]
    (M : ℕ) (hM : 0 < M) (p : Fin M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (U : Fin M → Matrix.unitaryGroup A ℂ) (V : Fin M → Matrix.unitaryGroup B ℂ)
    (epsilon : ℝ) (he : 0 ≤ epsilon) :
    P67.smoothConditionalMaxEntropyExtended rho (epsilon * Real.sqrt 2) ≤
      P67.smoothConditionalMaxEntropyExtended
        (∑ i, (p i : ℂ) •
          (Matrix.kronecker (U i : Matrix A A ℂ) (V i : Matrix B B ℂ) * rho *
            (Matrix.kronecker (U i : Matrix A A ℂ) (V i : Matrix B B ℂ))ᴴ)) epsilon := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P47

end
