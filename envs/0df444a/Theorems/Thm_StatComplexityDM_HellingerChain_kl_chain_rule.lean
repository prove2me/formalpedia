-- Prove2me | Theorems.Thm_StatComplexityDM_HellingerChain_kl_chain_rule
-- name    : StatComplexityDM.HellingerChain.kl_chain_rule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:37.375864+00:00
-- url     : https://prove2.me/theorems/8f4a14c4-807c-4187-bd77-7b4380827523
-- title:
--   Proof of Lemma A.13, p. 73 — chain rule D_KL(Q ∥ P) = E_Q[Σᵢ D_KL(Q⁽ⁱ⁾(· | X₁:ᵢ₋₁) ∥ P⁽ⁱ⁾(· | X₁:ᵢ₋₁))] for sequential laws
-- statement:
--   Let $\mathcal X_1, \dots, \mathcal X_n$ be finite sets and let $P = (P^{(i)})$ and $Q = (Q^{(i)})$ be families of sequential kernels, $P^{(i)}(\cdot \mid x_{1:i-1})$ a probability distribution on $\mathcal X_i$ depending only on the prefix $x_{1:i-1}$. Let $\mathbb P$ and $\mathbb Q$ be the laws of $X_1, \dots, X_n$ under $X_i \sim P^{(i)}(\cdot \mid X_{1:i-1})$ and $X_i \sim Q^{(i)}(\cdot \mid X_{1:i-1})$. Then, with $D_{\mathrm{KL}}$ taking values in $[0, +\infty]$,
--   $$
--   D_{\mathrm{KL}}(\mathbb Q \,\|\, \mathbb P) = \mathbb E_{\mathbb Q}\Big[\sum_{i=1}^n D_{\mathrm{KL}}\big(Q^{(i)}(\cdot \mid X_{1:i-1}) \,\|\, P^{(i)}(\cdot \mid X_{1:i-1})\big)\Big].
--   $$
--   Here $D_{\mathrm{KL}}(p\,\|\,q) = \sum_a p(a)\log\frac{p(a)}{q(a)}$ if $p$ is absolutely continuous with respect to $q$, and $+\infty$ otherwise.
--
--   The proof of Lemma A.13 uses this identity in both of its parts: for Term I of (97) with the mixture kernels $P_\lambda$ in place of $P$, and for (98) with the roles of $P$ and $Q$ exchanged.
--
--   **Formalization Note** Finite alphabets. The expectation is the sum over full sequences $x$ of $\mathbb Q(x)$ times the inner sum, computed in $[0, +\infty]$ with $0 \cdot \infty = 0$, so a sequence of $\mathbb Q$-probability zero contributes nothing even if a conditional divergence along it is infinite. The platform's measure-theoretic chain rule for KL divergence uses Markov kernels on measurable spaces, a different representation; this is the finite sequential form.
-- source:
--   arXiv:2112.13487v3, App. A.2, proof of Lemma A.13, Term I, p. 73 ("follows from the chain rule for KL divergence"); p. 75

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_StatComplexityDM_HellingerChain_SeqLaw

namespace StatComplexityDM.HellingerChain

open FoundationsRL.GeneralDM

/-- The chain rule for KL divergence used in the proof of Lemma A.13 (arXiv:2112.13487v3,
App. A.2, p. 73, Term I; p. 75), finite alphabets: for sequential laws,
`D_KL(Q ∥ P) = E_Q[Σ_{i=1}^n D_KL(Q^{(i)}(· | X_{1:i−1}) ∥ P^{(i)}(· | X_{1:i−1}))]`,
both sides in `[0, ∞]`. The expectation weights each sequence by `Q(x)` as an extended
nonnegative real, so a sequence of `Q`-probability zero contributes `0` even when a
conditional divergence along it is `+∞`. -/
theorem kl_chain_rule {n : ℕ} {X : Fin n → Type*} [∀ i, Fintype (X i)]
    [∀ i, DecidableEq (X i)]
    (P Q : (i : Fin n) → ((j : Fin n) → X j) → X i → ℝ)
    (hP : IsSeqKernel P) (hQ : IsSeqKernel Q) :
    klDivDiscrete (seqLaw Q) (seqLaw P) =
      ∑ x : (j : Fin n) → X j,
        ENNReal.ofReal (seqLaw Q x) * ∑ i, klDivDiscrete (Q i x) (P i x) := by sorry

end StatComplexityDM.HellingerChain
