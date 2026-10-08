-- Prove2me | Theorems.Thm_RobustDP_Discounted_theorem5b_fixed_point
-- name    : RobustDP.Discounted.theorem5b_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:45:46.984997+00:00
-- url     : https://prove2.me/theorems/aff6c2bb-f93f-46f3-96b7-94f89d7792a1
-- title:
--   Theorem 5(b) — for D = ∏ₛ D(s), L_D V = V has a unique bounded solution, the robust value over Markov policies with rules in D
-- statement:
--   Let $(\mathcal S,\mathcal A,\mathcal P,r,\lambda)$ be a discounted ambiguous MDP, and for every state $s$ let $\mathcal D(s)\subseteq\mathcal A(s)$ be nonempty; put $\mathcal D=\prod_{s\in\mathcal S}\mathcal D(s)$. Define
--   $$W(s)=\sup_{\{\pi:\,d^\pi_t\in\mathcal D\}}\ \inf_{\mathbf P\in\mathcal T^\pi}\mathbf E^{\mathbf P}\Big[\sum_{t=0}^\infty\lambda^t r(s_t,d_t(h_t),s_{t+1})\Big],$$
--   the supremum over deterministic Markov policies $\pi=(d_0,d_1,\dots)$ with every $d_t\in\mathcal D$. Then $W$ is bounded, $\mathcal L_{\mathcal D}W=W$, and $W$ is the only bounded solution of $\mathcal L_{\mathcal D}V=V$.
--
--   With $\mathcal D=\prod_s\mathcal A(s)$ this identifies the solution of the robust optimality equation with the robust value over deterministic Markov policies.
--
--   **Formalization Note** The page states Theorem 5(b) for an arbitrary set $\mathcal D$ of decision rules. Its proof of the upper bound (28) picks one $d\in\mathcal D$ that is $\epsilon$-greedy at every state simultaneously, which needs $\mathcal D$ closed under state-wise pasting; for a non-product $\mathcal D$ the statement fails (two states, $\mathcal D=\{d_1\equiv a,\ d_2\equiv b\}$). It is stated here for product sets $\mathcal D=\prod_s\mathcal D(s)$, which include both cases the paper uses ($\mathcal D=\{d\}$ and $\mathcal D=\prod_s\mathcal A(s)$). "Unique solution" is uniqueness among bounded functions.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 9, Theorem 5(b); proof pp. 10–11, (24)–(28)

import Mathlib
import Definitions.Def_RobustDP_Discounted_Model
import Definitions.Def_RobustDP_Discounted_Value
import Definitions.Def_RobustDP_Discounted_Bellman

namespace RobustDP.Discounted

theorem theorem5b_fixed_point {S A : Type*} [Countable S] [Countable A] (M : Model S A)
    (Dset : S → Set A) (hDne : ∀ s, (Dset s).Nonempty) (hDsub : ∀ s, Dset s ⊆ M.Aset s) :
    let W : S → ℝ := fun s => ⨆ f : ℕ → productRules M Dset, V M (markovPolicy M (fun n => (f n).1)) s
    IsBounded W ∧ L M (productRules M Dset) W = W ∧
      ∀ U : S → ℝ, IsBounded U → L M (productRules M Dset) U = U → U = W := by sorry

end RobustDP.Discounted
