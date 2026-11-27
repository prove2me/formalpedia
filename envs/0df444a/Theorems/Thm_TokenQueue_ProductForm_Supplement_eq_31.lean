-- Prove2me | Theorems.Thm_TokenQueue_ProductForm_Supplement_eq_31
-- name    : TokenQueue.ProductForm.Supplement.eq_31
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T18:18:50.820673+00:00
-- url     : https://prove2.me/theorems/5fcf75cd-8290-4915-88ec-8bd87f04166a
-- title:
--   Eq. (31), p. 25 — given the descriptor, the inactive customers' type counts per block are independent multinomial(n_j; θ_{·,j})
-- statement:
--   Consider the token-based central queue with customer types $\mathcal C$, tokens $\mathcal T=\{t_1,\dots,t_K\}$, Poisson arrival rates $\lambda_c>0$, compatible token sets $\mathcal T_c\neq\emptyset$, a randomised assignment rule satisfying Condition 1, departure rates $\mu_{T_j}=\eta(\phi)s_j(T_1,\dots,T_j)$ satisfying Condition 2 with $k(T_1,\dots,T_j)>0$, and suppose the queue is stable (the series (11) converges). Let $Q$ be any stationary law of the customer-level chain (each customer's type and token kept; see the definitions item), and write $\mathbb E$, $\mathbb P$ for expectation and probability under $Q$. For a descriptor $x=(T_1,n_1,\dots,T_i,n_i)$ put $\alpha_j=\lambda_{\mathcal U(\{T_1,\dots,T_j\})}/k(T_1,\dots,T_j)$ and $\theta_{c,j}=\lambda_c\mathbb 1\{c\in\mathcal U(\{T_1,\dots,T_j\})\}/\lambda_{\mathcal U(\{T_1,\dots,T_j\})}$, where $\mathcal U(S)=\{c:\mathcal T_c\subseteq S\}$.
--
--   Then, for every descriptor $x=(T_1,n_1,\dots,T_i,n_i)$ and all nonnegative integers $n^{(c)}_j$ with $\sum_{c\in\mathcal C}n^{(c)}_j=n_j$ for each $j$,
--   $$\mathbb P\Bigl(\mathrm{desc}=x,\ N^{(c)}_j=n^{(c)}_j\ \forall j,c\Bigr)=\mathbb P(\mathrm{desc}=x)\prod_{j=1}^{i}\frac{n_j!}{\prod_{c\in\mathcal C}n^{(c)}_j!}\prod_{c\in\mathcal C}\theta_{c,j}^{\,n^{(c)}_j}.\tag{31}$$
--   That is, given the descriptor, the types of the $n_j$ inactive customers of each block are multinomial with parameters $\theta_{\cdot,j}$, independently across blocks.
--
--   This is the step of the proof of Theorem 2 (Appendix B) that turns the descriptor-level product form into the joint law of the per-type counts.
--
--   **Formalization Note** The conditional probability of (31) is stated multiplicatively, so no conditioning on a null event is needed; the conditioning is on the whole descriptor $x$, as in (32).
--
--   Differences from the source:
--   - encoding: the model of §3 with Conditions 1–2 (types with no compatible token and k = 0 not discussed) → the published hypotheses P.Standing (with T_c ≠ ∅) and KPos (k(T1,…,Tj) > 0 for non-empty token sequences), as in the published Theorem 1; reason: a type with T_c = ∅ is never served, so no stationary law exists and the theorem has no instance there; k > 0 only excludes the cases where α_j and the weights (10) divide by zero
--   - reading: the queue is stable → Summable (weight P): the series in (11) converges; reason: §4.4, p. 9: stability is the convergence of (11); this is the published goal's reading
--   - reading: E and P refer to the stationary system (a stationary distribution of the model with customer types kept) → the statement holds for every Q with IsStationaryLaw P Q: a probability law on customer-level states satisfying the §3 invariant, with summable rows and inflows, in global balance with the forward customer-level rates crate; reason: the performance measures of §5 need the types of the customers, which the descriptor x forgets; uniqueness of the stationary law is not assumed, so the claim is made for each one
--   - encoding: P(∩{N_j^(c) = n_j^(c)} | ∩{N_j = n_j}) = RHS → Q(desc = x ∧ N_j^(c) = n_j^(c) ∀ j,c) = Q(desc = x) · RHS; reason: equivalent when Q(desc = x) > 0, and both sides vanish otherwise
--   - reading: conditioning on {N_j = n_j}, j = 1,…,i → conditioning on the descriptor x = (T1,n1,…,Ti,ni); reason: θ_{c,j} depends on T1,…,Tj, so the tokens are fixed by the context; (32) on the same page conditions on x
--   - reading: the printed factor ∏_{c∈C} θ_c^{n_{c,j}} → ∏_{c∈C} θ_{c,j}^{n_j^(c)}; reason: notation slip in (31): θ_c and n_{c,j} are not defined anywhere, the parameters were just introduced as θ_{c,j} and the counts as n_j^(c), and (32) on the same page uses (θ_{c,j} z_{c,j})^{n_{c,j}}
-- source:
--   Ayesta, Bodas, Dorsman, Verloop, A token-based central queue with order-independent service rates, arXiv:1902.02137v1, p. 25, Appendix B, Eq. (31)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_TokenQueue_ProductForm_Model
import Definitions.Def_TokenQueue_ProductForm_Supplement_CustomerChain

namespace TokenQueue.ProductForm.Supplement

open Finset

/-- **Eq. (31)**, p. 25 (proof of Theorem 2). In every stationary law `Q` of the customer-level
chain, given the descriptor `x = (T₁,n₁,…,T_i,n_i)`, the type counts `(N_j^{(c)})_{c}` of the
`n_j` inactive customers of block `j` are multinomial with population `n_j` and parameters
`θ_{c,j}`, independently across blocks; stated multiplicatively. -/
theorem eq_31 {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (h1 : Condition1 P) (h2 : Condition2 P) (hk : KPos P)
    (hstab : Summable (weight P)) (Q : CState C T → ℝ) (hQ : IsStationaryLaw P Q)
    (x : State T) (n : Fin x.1.length → C → ℕ) (hn : ∀ j, ∑ c, n j c = (x.1.get j).2) :
    prob Q (fun y => desc y = x.1 ∧ ∀ j : Fin x.1.length, ∀ c, Nseg y j c = n j c) =
      prob Q (fun y => desc y = x.1) *
        ∏ j : Fin x.1.length,
          (((x.1.get j).2.factorial : ℝ) / ∏ c, ((n j c).factorial : ℝ)) *
            ∏ c, theta P ((toks x.1).take (j + 1)) c ^ n j c := by sorry

end TokenQueue.ProductForm.Supplement
