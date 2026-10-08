-- Prove2me | Theorems.Thm_SuttonTD_Convergence_key_matrix_posDef
-- name    : SuttonTD.Convergence.key_matrix_posDef
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:23:45.6249+00:00
-- url     : https://prove2.me/theorems/af14487c-af09-4b5f-a959-f5b7e6f1121e
-- title:
--   $D(I-Q)$ is positive definite (§4.1, p. 27)
-- statement:
--   Let $C$ be an absorbing Markov chain with nonterminal block $Q$, let $\mu$ be a start distribution, and let $d$ be given by (7), $d^\top=\mu^\top(I-Q)^{-1}$, with $D=\operatorname{diag}(d)$. If every $d_i$ is strictly positive, then
--
--   $$D(I-Q)\ \text{is positive definite: } y^\top D(I-Q)\,y>0 \text{ for every real } y\ne0 .$$
--
--   This is the step that makes the mean TD(0) iteration contractive for small $\alpha$.
--
--   **Formalization Note** The hypothesis $d_i>0$ is the paper's "Each $d_i$ is strictly positive, because any state for which $d_i=0$ has no probability of being visited and can be discarded" (p. 25). The paper's proof via the Lemma relies on its weakened notion of diagonal dominance; the statement itself is true but needs an argument combining weak dominance with reachability from the support of $\mu$.
-- source:
--   Sutton (1988), Machine Learning 3:9–44, §4.1, p. 27 (PDF p. 19)

import Definitions.Def_SuttonTD_Convergence_AbsorbingChain
import Definitions.Def_SuttonTD_Convergence_IsPosDefReal
open Matrix

namespace SuttonTD.Convergence

/-- **`D(I − Q)` is positive definite** (Sutton 1988, §4.1, p. 27, PDF p. 19). Let `C` be an
absorbing Markov chain with nonterminal block `Q`, let `μ` be a distribution of starting
probabilities, and let `d` be given by (7), `dᵀ = μᵀ(I − Q)⁻¹`. If every `d_i` is strictly
positive (p. 25), then `D(I − Q)` is positive definite in the paper's sense, where `D = diag(d)`.

Formalization Note: the hypothesis `0 < d_i` is the paper's "Each `d_i` is strictly positive,
because any state for which `d_i = 0` has no probability of being visited and can be discarded"
(p. 25). The statement is the paper's; its proof on p. 27 via the Lemma does not go through as
printed (with the standard notion, `S = D(I−Q) + (D(I−Q))ᵀ` need not be strictly diagonally
dominant), so a proof must use weak dominance together with reachability from the support of `μ`. -/
theorem key_matrix_posDef {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T]
    (C : AbsorbingChain N T) (μ : N → ℝ) (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : ∑ i, μ i = 1)
    (hd : ∀ i, 0 < (μ ᵥ* (1 - C.Q)⁻¹) i) :
    IsPosDefReal (diagonal (μ ᵥ* (1 - C.Q)⁻¹) * (1 - C.Q)) := by sorry

end SuttonTD.Convergence
