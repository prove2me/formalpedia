-- Prove2me | Theorems.Thm_TokenQueue_ProductForm_Supplement_theorem_6
-- name    : TokenQueue.ProductForm.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:20:44.183592+00:00
-- url     : https://prove2.me/theorems/d21abd3c-2f3d-41ca-8a09-4a7b79d2770f
-- title:
--   Theorem 6, p. 11 (corrected: η constant from |𝒯_c|+1 on; series (22) assumed convergent) — LST of the time-till-token W_c
-- statement:
--   Consider the token-based central queue with customer types $\mathcal C$, tokens $\mathcal T=\{t_1,\dots,t_K\}$, Poisson arrival rates $\lambda_c>0$, compatible token sets $\mathcal T_c\neq\emptyset$, a randomised assignment rule satisfying Condition 1, departure rates $\mu_{T_j}=\eta(\phi)s_j(T_1,\dots,T_j)$ satisfying Condition 2 with $k(T_1,\dots,T_j)>0$, and suppose the queue is stable (the series (11) converges). Let $Q$ be any stationary law of the customer-level chain (each customer's type and token kept; see the definitions item), and write $\mathbb E$, $\mathbb P$ for expectation and probability under $Q$. For a descriptor $x=(T_1,n_1,\dots,T_i,n_i)$ put $\alpha_j=\lambda_{\mathcal U(\{T_1,\dots,T_j\})}/k(T_1,\dots,T_j)$ and $\theta_{c,j}=\lambda_c\mathbb 1\{c\in\mathcal U(\{T_1,\dots,T_j\})\}/\lambda_{\mathcal U(\{T_1,\dots,T_j\})}$, where $\mathcal U(S)=\{c:\mathcal T_c\subseteq S\}$.
--
--   Assume moreover that $\eta(n)=\eta(|\mathcal T_c|+1)$ for every $n\ge|\mathcal T_c|+1$ (while a type-$c$ customer waits, at least $|\mathcal T_c|+1$ customers are present). Let $W_c$ be the time-till-token of a type-$c$ customer arriving to the stationary system: the time from its arrival until it holds a token. Then for every complex $s$ with $\operatorname{Re}s>0$ for which the series below converges,
--   $$\mathbb E\bigl[e^{-sW_c}\bigr]=\sum_{i=0}^{K}\sum_{(T_1,\dots,T_i)\in\mathcal T^i}\sum_{(n_1,\dots,n_i)\in\mathbb N_0^i}\pi((0))\frac{\Pi_\lambda(\{T_1,\dots,T_i\})}{\Pi_k(T_1,\dots,T_i)}\prod_{j=1}^{i}\frac1{\eta(j)}\prod_{j=1}^{n_1+\dots+n_i}\frac1{\eta(i+j)}\prod_{j=1}^{i}\Bigl(\alpha_j\Bigl(1-\frac{s\,\mathbb 1\{c\in\mathcal U(\{T_1,\dots,T_j\})\}}{\lambda_{\mathcal U(\{T_1,\dots,T_j\})}}\Bigr)\Bigr)^{n_j}.\tag{22}$$
--
--   Theorem 6 gives the distribution of the time a customer waits for a token, which in many applications of the model is its waiting time.
--
--   **Formalization Note** The two corrections ($\eta$ constant from $|\mathcal T_c|+1$ on, convergence of the series) are explained below and in DISPROOF.md; the printed statement claims (22) for every $\eta$ and every $\operatorname{Re}s>0$.
--
--   Differences from the source:
--   - encoding: the model of §3 with Conditions 1–2 (types with no compatible token and k = 0 not discussed) → the published hypotheses P.Standing (with T_c ≠ ∅) and KPos (k(T1,…,Tj) > 0 for non-empty token sequences), as in the published Theorem 1; reason: a type with T_c = ∅ is never served, so no stationary law exists and the theorem has no instance there; k > 0 only excludes the cases where α_j and the weights (10) divide by zero
--   - reading: the queue is stable → Summable (weight P): the series in (11) converges; reason: §4.4, p. 9: stability is the convergence of (11); this is the published goal's reading
--   - reading: E and P refer to the stationary system (a stationary distribution of the model with customer types kept) → the statement holds for every Q with IsStationaryLaw P Q: a probability law on customer-level states satisfying the §3 invariant, with summable rows and inflows, in global balance with the forward customer-level rates crate; reason: the performance measures of §5 need the types of the customers, which the descriptor x forgets; uniqueness of the stationary law is not assumed, so the claim is made for each one
--   - encoding: Σ_{i=0}^{K} Σ_{(T1,…,Ti)∈T^i} Σ_{(n1,…,ni)∈N0^i} of the displayed term, with π((0)) given by (11) → HasSum over the published State T (lists of distinct tokens with counts) of the same term, with π((0)) = (Σ_x weight P x)^{-1}; reason: State T enumerates exactly the index set of the triple sum; HasSum asserts that the series converges unconditionally to the left-hand side, so no junk tsum value arises; (Σ_x weight)^{-1} equals (11) because the weight of (0) is 1
--   - reading: W_c, the time-till-token of a type-c customer, in the stationary system → the first-passage LST, from the state just after a tagged type-c arrival to a state drawn from Q, of the first time the tagged customer holds a token, in the customer-level chain (sum over first-passage jump paths); reason: Poisson arrivals see the stationary law (§5.3 uses this through Little's law); the jump-path sum is the LST of a first-passage time of the continuous-time chain
--   - correction: η(·) any function with η(j) > 0 (Condition 2) → η constant from |T_c|+1 on: ∀ j ≥ |T_c|+1, η(j) = η(|T_c|+1); reason: the printed formula is false for non-constant η: one type, one token, λ = 1, s([t]) = 1, η(n) = min(n,4) (stable, Conditions 1–2 hold) at s = 0.7 gives E[e^{-sW}] = 0.8071 by solving the first-passage equations, against 0.7958 from (22); for Theorem 7 the same instance gives 0.5470 against 0.4959 from (24). The proof's distributional Little law (21)/(23) needs the time-till-token (sojourn time) to be unaffected by later arrivals, which fails when the service speed η depends on the total number present; with constant η the two sides agree (0.7941 = 0.7941, 0.5882 = 0.5882 at η ≡ 2). While a type-c customer waits, all of T_c is held by customers ahead of it, so at least |T_c|+1 customers are present; if η is constant on those numbers the customers ahead evolve independently of later arrivals and (21) holds, whatever η(1),…,η(|T_c|) are (checked: one token, η = (1,2,2,…) and (3,2,2,…) give (22) exactly at s = 0.7, 0.7255 and 0.8353; η = (1,2,3,3,…) gives 0.7961 against 0.7879). See DISPROOF.md. Excluded cases: every η that is not constant on {|T_c|+1, |T_c|+2, …}
--   - correction: the identity holds for every s with Re s > 0 → for Re s > 0, if the series is summable, it converges to the LST; reason: for large |s| the right-hand side diverges while the LST is finite: one type, one token, λ = 1, s([t]) = 1, η ≡ 2, s = 3 gives terms of modulus π((0))/2 for every n; the identity is asserted wherever the series converges (on the disc |s − λ_c| < λ_c it always does). Excluded cases: the values of s where the printed series diverges, at which the printed equation has no meaning
-- source:
--   Ayesta, Bodas, Dorsman, Verloop, A token-based central queue with order-independent service rates, arXiv:1902.02137v1, p. 11, Theorem 6, Eq. (22); (21) p. 10

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_TokenQueue_ProductForm_Model
import Definitions.Def_TokenQueue_ProductForm_Supplement_CustomerChain

namespace TokenQueue.ProductForm.Supplement

open Finset

/-- **Theorem 6**, p. 11 (corrected: `η` constant on `{n : n ≥ |𝒯_c| + 1}`, the numbers of
customers present while a type-`c` customer waits, and the series (22) assumed convergent). For complex `s` with `Re s > 0`, the LST `E[e^{−sW_c}]` of the time-till-token of a
type-`c` customer arriving to the stationary system `Q` is the series (22). -/
theorem theorem_6 {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (h1 : Condition1 P) (h2 : Condition2 P) (hk : KPos P)
    (hstab : Summable (weight P)) (Q : CState C T → ℝ) (hQ : IsStationaryLaw P Q)
    (c : C) (hη : ∀ j, (P.tok c).card + 1 ≤ j → P.eta j = P.eta ((P.tok c).card + 1))
    (s : ℂ) (hs : 0 < s.re)
    (hsum : Summable (fun x : State T => (commonFactor P x.1 : ℂ) *
        ∏ j : Fin x.1.length,
          ((alpha P ((toks x.1).take (j + 1)) : ℂ) *
            (1 - s * (if P.tok c ⊆ ((toks x.1).take (j + 1)).toFinset then 1 else 0) /
              (lamU P ((toks x.1).take (j + 1)).toFinset : ℂ))) ^ (x.1.get j).2)) :
    HasSum (fun x : State T => (commonFactor P x.1 : ℂ) *
        ∏ j : Fin x.1.length,
          ((alpha P ((toks x.1).take (j + 1)) : ℂ) *
            (1 - s * (if P.tok c ⊆ ((toks x.1).take (j + 1)).toFinset then 1 else 0) /
              (lamU P ((toks x.1).take (j + 1)).toFinset : ℂ))) ^ (x.1.get j).2)
      (lstW P Q c s) := by sorry

end TokenQueue.ProductForm.Supplement
