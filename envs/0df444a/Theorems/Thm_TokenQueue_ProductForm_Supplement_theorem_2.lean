-- Prove2me | Theorems.Thm_TokenQueue_ProductForm_Supplement_theorem_2
-- name    : TokenQueue.ProductForm.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:19:31.89407+00:00
-- url     : https://prove2.me/theorems/ea7b86ce-1f2e-4279-8891-0a7ba90eb115
-- title:
--   Theorem 2, p. 9 — joint PGF (17) of the per-type numbers of inactive customers
-- statement:
--   Consider the token-based central queue with customer types $\mathcal C$, tokens $\mathcal T=\{t_1,\dots,t_K\}$, Poisson arrival rates $\lambda_c>0$, compatible token sets $\mathcal T_c\neq\emptyset$, a randomised assignment rule satisfying Condition 1, departure rates $\mu_{T_j}=\eta(\phi)s_j(T_1,\dots,T_j)$ satisfying Condition 2 with $k(T_1,\dots,T_j)>0$, and suppose the queue is stable (the series (11) converges). Let $Q$ be any stationary law of the customer-level chain (each customer's type and token kept; see the definitions item), and write $\mathbb E$, $\mathbb P$ for expectation and probability under $Q$. For a descriptor $x=(T_1,n_1,\dots,T_i,n_i)$ put $\alpha_j=\lambda_{\mathcal U(\{T_1,\dots,T_j\})}/k(T_1,\dots,T_j)$ and $\theta_{c,j}=\lambda_c\mathbb 1\{c\in\mathcal U(\{T_1,\dots,T_j\})\}/\lambda_{\mathcal U(\{T_1,\dots,T_j\})}$, where $\mathcal U(S)=\{c:\mathcal T_c\subseteq S\}$.
--
--   Write $N^{(c)}$ for the number of inactive type-$c$ customers. Then for all complex $z_c$ with $|z_c|<1$,
--   $$\mathbb E\Bigl[\prod_{c\in\mathcal C}z_c^{N^{(c)}}\Bigr]=\sum_{i=0}^{K}\sum_{(T_1,\dots,T_i)\in\mathcal T^i}\sum_{(n_1,\dots,n_i)\in\mathbb N_0^i}\pi((0))\frac{\Pi_\lambda(\{T_1,\dots,T_i\})}{\Pi_k(T_1,\dots,T_i)}\prod_{j=1}^{i}\frac1{\eta(j)}\prod_{j=1}^{n_1+\dots+n_i}\frac1{\eta(i+j)}\prod_{j=1}^{i}\Bigl(\alpha_j\sum_{c\in\mathcal C}\theta_{c,j}z_c\Bigr)^{n_j},\tag{17}$$
--   the series converging (unconditionally) to the left-hand side.
--
--   Theorem 2 gives the joint distribution of the per-type numbers of waiting customers; setting all $z_c=z$ gives the PGF of the total number of inactive customers (Corollary 3).
--
--   Differences from the source:
--   - encoding: the model of §3 with Conditions 1–2 (types with no compatible token and k = 0 not discussed) → the published hypotheses P.Standing (with T_c ≠ ∅) and KPos (k(T1,…,Tj) > 0 for non-empty token sequences), as in the published Theorem 1; reason: a type with T_c = ∅ is never served, so no stationary law exists and the theorem has no instance there; k > 0 only excludes the cases where α_j and the weights (10) divide by zero
--   - reading: the queue is stable → Summable (weight P): the series in (11) converges; reason: §4.4, p. 9: stability is the convergence of (11); this is the published goal's reading
--   - reading: E and P refer to the stationary system (a stationary distribution of the model with customer types kept) → the statement holds for every Q with IsStationaryLaw P Q: a probability law on customer-level states satisfying the §3 invariant, with summable rows and inflows, in global balance with the forward customer-level rates crate; reason: the performance measures of §5 need the types of the customers, which the descriptor x forgets; uniqueness of the stationary law is not assumed, so the claim is made for each one
--   - encoding: Σ_{i=0}^{K} Σ_{(T1,…,Ti)∈T^i} Σ_{(n1,…,ni)∈N0^i} of the displayed term, with π((0)) given by (11) → HasSum over the published State T (lists of distinct tokens with counts) of the same term, with π((0)) = (Σ_x weight P x)^{-1}; reason: State T enumerates exactly the index set of the triple sum; HasSum asserts that the series converges unconditionally to the left-hand side, so no junk tsum value arises; (Σ_x weight)^{-1} equals (11) because the weight of (0) is 1
-- source:
--   Ayesta, Bodas, Dorsman, Verloop, A token-based central queue with order-independent service rates, arXiv:1902.02137v1, p. 9, Theorem 2, Eq. (17)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_TokenQueue_ProductForm_Model
import Definitions.Def_TokenQueue_ProductForm_Supplement_CustomerChain

namespace TokenQueue.ProductForm.Supplement

open Finset

/-- **Theorem 2**, p. 9. For complex `z_c` with `|z_c| < 1`, the joint PGF
`E[∏_c z_c^{N^{(c)}}]` of the numbers of inactive customers per type under any stationary law `Q`
of the customer-level chain is the series (17) over all descriptors. -/
theorem theorem_2 {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (h1 : Condition1 P) (h2 : Condition2 P) (hk : KPos P)
    (hstab : Summable (weight P)) (Q : CState C T → ℝ) (hQ : IsStationaryLaw P Q)
    (z : C → ℂ) (hz : ∀ c, ‖z c‖ < 1) :
    HasSum (fun x : State T => (commonFactor P x.1 : ℂ) *
        ∏ j : Fin x.1.length,
          ((alpha P ((toks x.1).take (j + 1)) : ℂ) *
            ∑ c, (theta P ((toks x.1).take (j + 1)) c : ℂ) * z c) ^ (x.1.get j).2)
      (∑' y, (Q y : ℂ) * ∏ c, z c ^ Ntot y c) := by sorry

end TokenQueue.ProductForm.Supplement
