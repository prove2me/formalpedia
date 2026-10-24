-- Prove2me | Theorems.Thm_RLInference_QValueCLT_I_sub_gamma_PtildePrime_invertible
-- name    : RLInference.QValueCLT.I_sub_gamma_PtildePrime_invertible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:13:09.031165+00:00
-- url     : https://prove2.me/theorems/b0ff636e-3177-4a3c-80ca-6a52057ac527
-- title:
--   Proof of Theorem 1, p. 36 — ∂F/∂Q′ = I − γP̃′ is invertible for stochastic P′ and Q′ with a unique argmax
-- statement:
--   Let $\mathcal S,\mathcal A$ be finite nonempty sets and $0\le\gamma<1$. Let $P'(\cdot\mid s,a)$ be a stochastic array: nonnegative entries, and each row summing to one. Let $Q'$ be a function on $\mathcal S\times\mathcal A$ such that for every state $k$ the maximizer of $l\mapsto Q'(k,l)$ is unique. Define the $N\times N$ matrix
--
--   $$\tilde P'((s,a),(k,l))=P'(k\mid s,a)\,\mathbb 1\Big(Q'(k,l)=\max_{u\in\mathcal A}Q'(k,u)\Big).$$
--
--   Then $I-\gamma\tilde P'$ is invertible.
--
--   In the proof of Theorem 1, $I-\gamma\tilde P'$ is the Jacobian $\partial F/\partial Q'$ of the fixed-point map $F(Q',r',P')=Q'-\mathcal T_{r',P'}(Q')$. Its invertibility is what allows the implicit function theorem to be applied.
--
--   **Formalization Note.** The paper states the claim for $Q'$ in the neighbourhood $\Omega$ of $Q$ on which every argmax is unique; this is the hypothesis on $Q'$. "$P'$ stochastic" is a disclosed pin: the paper says "since all rows of $\tilde P'$ sum up to one, $\tilde P'$ can be interpreted as the transition matrix of a Markov chain", which presupposes nonnegative entries, and the claim is used at $P'=P$. Rows summing to one alone would not give invertibility.
-- source:
--   Zhu, Dong & Lam, Uncertainty Quantification and Exploration for Reinforcement Learning, arXiv:1910.05471v3, p. 36, App. A.1, first paragraph (P̃′ defined on p. 35)

import Mathlib
import Definitions.Def_RLInference_QValueCLT_Setting
open MeasureTheory ProbabilityTheory Filter Matrix Topology

namespace RLInference.QValueCLT

theorem I_sub_gamma_PtildePrime_invertible {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (P' : S × A → S → ℝ) (hP'_nonneg : ∀ x k, 0 ≤ P' x k) (hP'_sum : ∀ x, ∑ k, P' x k = 1)
    (Q' : S × A → ℝ) (hQ' : ∀ k : S, ∃ a : A, ∀ a' : A, a' ≠ a → Q' (k, a') < Q' (k, a)) :
    IsUnit (1 - γ • PtildePrime P' Q') := by sorry

end RLInference.QValueCLT
