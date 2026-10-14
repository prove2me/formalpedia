-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_adversary_claim2_one_query
-- name    : QAlgorithms.DeWolf.adversary_claim2_one_query
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:42:42.625197+00:00
-- url     : https://prove2.me/theorems/82aca644-cd01-4c27-abfe-d15c90960a03
-- title:
--   Generalized adversary method: one query changes the progress measure by at most 2 max_i ‖Γ_i‖
-- statement:
--   Let $f : D \to \{0,1\}$ with $D \subseteq \{0,1\}^N$, let $\mathcal A = U_T O_x U_{T-1} \cdots U_1 O_x U_0$ be any $T$-query quantum algorithm with input-independent unitaries $U_t$ and the standard query $O_x : |i,b\rangle \mapsto |i, b\oplus x_i\rangle$, and let $|\psi_x^t\rangle$ be its state after $U_t$ on input $x$, so that $|\psi_x^{t+1}\rangle = U_{t+1} O_x |\psi_x^t\rangle$. Let $\Gamma$ be an adversary matrix for $f$, let $\alpha \in \mathbb C^D$ be a unit vector, and let $S_t = \sum_{x,y \in D} \Gamma_{xy}\, \alpha_x^* \alpha_y \langle \psi_x^t | \psi_y^t \rangle$.
--
--   For $i \in [N]$ let $\Gamma_i$ be the $|D| \times |D|$ matrix obtained from $\Gamma$ by setting $\Gamma_{xy}$ to $0$ whenever $x_i = y_i$. Then for all $t \in \{0, \dots, T-1\}$,
--
--   $$
--   |S_t - S_{t+1}| \le 2 \max_{i \in [N]} \|\Gamma_i\|,
--   $$
--
--   with $\|\cdot\|$ the operator norm.
--
--   This bounds how much a single query can change the progress measure, and combined with Claim 1 yields the generalized adversary lower bound.
--
--   **Formalization Note** The maximum is a supremum over `Fin N`; for $N = 0$ it is $0$, and then $D$ has at most one element, $\Gamma = 0$ and both sides vanish. No error assumption on the algorithm is needed.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 112, §12.1, Claim 2. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Adversary
set_option autoImplicit false

namespace QAlgorithms.DeWolf


/-- de Wolf §12.1, Claim 2 (PDF p. 112): for a `T`-query algorithm `A`, an adversary matrix `Γ`
for `f` and a unit vector `α` of weights on `D`, one query changes the progress measure by at most
twice the largest operator norm of the masked matrices `Γ_i` (`Γ` with `Γ_xy` set to `0` when
`x_i = y_i`): for all `t ∈ {0, …, T−1}`, `|S_t − S_{t+1}| ≤ 2 max_{i ∈ [N]} ‖Γ_i‖`. -/
theorem adversary_claim2_one_query {N : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (f : (Fin N → Bool) → Bool) (D : Finset (Fin N → Bool)) (Γ : Matrix D D ℝ)
    (hΓ : IsAdversaryMatrix f D Γ) (α : D → ℂ) (hα : ∑ x : D, ‖α x‖ ^ 2 = 1)
    (A : QueryAlg (Fin N) Bool W T) (t : Fin T) :
    ‖progressMeasure A Γ α t.castSucc - progressMeasure A Γ α t.succ‖ ≤
      2 * maxMaskedNorm Γ := by
  sorry





end QAlgorithms.DeWolf
