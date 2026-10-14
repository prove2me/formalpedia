-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_adversary_claim1_final_progress
-- name    : QAlgorithms.DeWolf.adversary_claim1_final_progress
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:42:45.199468+00:00
-- url     : https://prove2.me/theorems/0fb5d8a9-5d69-4252-99b9-644ce487a185
-- title:
--   Generalized adversary method: the final progress measure is small
-- statement:
--   Let $f : D \to \{0,1\}$ with $D \subseteq \{0,1\}^N$. Let $\mathcal A = U_T O_x U_{T-1} \cdots U_1 O_x U_0$ be a $T$-query quantum algorithm: the unitaries $U_0, \dots, U_T$ act on a query register $|i, b\rangle$ ($i \in [N]$, $b \in \{0,1\}$) together with a workspace, do not depend on the input, and are applied to a fixed start state; $O_x : |i,b\rangle \mapsto |i, b \oplus x_i\rangle$ is the standard query. Write $|\psi_x^t\rangle$ for the state after $U_t$ on input $x$. Suppose that $\mathcal A$, followed by a computational-basis measurement and a fixed output rule, outputs $f(x)$ with probability at least $1-\varepsilon$ for every $x \in D$, where $0 \le \varepsilon < 1/2$.
--
--   Let $\Gamma$ be an adversary matrix for $f$ (a real symmetric $|D| \times |D|$ matrix with $\Gamma_{xy} = 0$ whenever $f(x) = f(y)$), let $\alpha \in \mathbb C^D$ with $\sum_{x \in D} |\alpha_x|^2 = 1$, and let $S_t = \sum_{x,y \in D} \Gamma_{xy}\, \alpha_x^* \alpha_y \langle \psi_x^t | \psi_y^t \rangle$ be the progress measure. Then
--
--   $$
--   |S_T| \le 2\sqrt{\varepsilon(1-\varepsilon)}\, \|\Gamma\|,
--   $$
--
--   where $\|\Gamma\|$ is the operator norm (largest singular value) of $\Gamma$.
--
--   Together with $|S_0| = \|\Gamma\|$ for a suitable $\alpha$, this shows that the progress measure must drop substantially during any bounded-error algorithm.
--
--   **Formalization Note** The algorithm is `QueryAlg`, whose start state is an arbitrary unit vector (equivalent to the source's $|0^m\rangle$ followed by $U_0$); the output is an arbitrary function of the basis measurement outcome.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 112, §12.1, Claim 1. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Adversary
set_option autoImplicit false

namespace QAlgorithms.DeWolf

/-- de Wolf §12.1, Claim 1 (PDF p. 112): let `A` be a `T`-query algorithm that computes
`f : D → {0,1}` with error probability at most `ε < 1/2` on every `x ∈ D`, let `Γ` be an adversary
matrix for `f` and `α` a unit vector of weights on `D`. Then the final progress measure satisfies
`|S_T| ≤ 2 √(ε(1−ε)) ‖Γ‖`. -/
theorem adversary_claim1_final_progress {N : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (f : (Fin N → Bool) → Bool) (D : Finset (Fin N → Bool)) (Γ : Matrix D D ℝ)
    (hΓ : IsAdversaryMatrix f D Γ) (α : D → ℂ) (hα : ∑ x : D, ‖α x‖ ^ 2 = 1) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) (A : QueryAlg (Fin N) Bool W T)
    (out : (Fin N × Bool) × W → Bool) (hA : A.ComputesWithError out D f ε) :
    ‖progressMeasure A Γ α (Fin.last T)‖ ≤ 2 * Real.sqrt (ε * (1 - ε)) * specNorm Γ := by
  sorry






end QAlgorithms.DeWolf
