-- Prove2me | Theorems.Thm_TokenQueue_ProductForm_Supplement_theorem_7
-- name    : TokenQueue.ProductForm.Supplement.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:21:18.121333+00:00
-- url     : https://prove2.me/theorems/ac20c145-01dc-4b1a-9875-74c1a7d3f7e0
-- title:
--   Theorem 7, p. 11 (corrected: exponent Σ_j 1{c_j=c}, denominator λ_U, η constant, series convergent) — LST of the sojourn time S_c
-- statement:
--   Consider the token-based central queue with customer types $\mathcal C$, tokens $\mathcal T=\{t_1,\dots,t_K\}$, Poisson arrival rates $\lambda_c>0$, compatible token sets $\mathcal T_c\neq\emptyset$, a randomised assignment rule satisfying Condition 1, departure rates $\mu_{T_j}=\eta(\phi)s_j(T_1,\dots,T_j)$ satisfying Condition 2 with $k(T_1,\dots,T_j)>0$, and suppose the queue is stable (the series (11) converges). Let $Q$ be any stationary law of the customer-level chain (each customer's type and token kept; see the definitions item), and write $\mathbb E$, $\mathbb P$ for expectation and probability under $Q$. For a descriptor $x=(T_1,n_1,\dots,T_i,n_i)$ put $\alpha_j=\lambda_{\mathcal U(\{T_1,\dots,T_j\})}/k(T_1,\dots,T_j)$ and $\theta_{c,j}=\lambda_c\mathbb 1\{c\in\mathcal U(\{T_1,\dots,T_j\})\}/\lambda_{\mathcal U(\{T_1,\dots,T_j\})}$, where $\mathcal U(S)=\{c:\mathcal T_c\subseteq S\}$.
--
--   Assume moreover that $\eta$ is constant on $\{1,2,\dots\}$ and that type-$c$ customers depart in the order of their arrival: in every state reachable from the empty system, a type-$c$ customer has departure rate $0$ while an earlier type-$c$ customer is present. Let $S_c$ be the sojourn time of a type-$c$ customer arriving to the stationary system, $g_j$ the type of the holder of $T_j$ and $G_{c_1,\dots,c_i}(x)=\mathbb P(g_1=c_1,\dots,g_i=c_i\mid\mathrm{desc}=x)$. Then for every complex $s$ with $\operatorname{Re}s>0$ for which the series below converges,
--   $$\mathbb E\bigl[e^{-sS_c}\bigr]=\sum_{i=0}^{K}\sum_{(T_1,\dots,T_i)\in\mathcal T^i}\sum_{(n_1,\dots,n_i)\in\mathbb N_0^i}\pi((0))\frac{\Pi_\lambda(\{T_1,\dots,T_i\})}{\Pi_k(T_1,\dots,T_i)}\prod_{j=1}^{i}\frac1{\eta(j)}\prod_{j=1}^{n_1+\dots+n_i}\frac1{\eta(i+j)}\Bigl(\sum_{(c_1,\dots,c_i)\in\mathcal C^i}G_{c_1,\dots,c_i}(x)\Bigl(\frac{\lambda_c-s}{\lambda_c}\Bigr)^{\sum_{j=1}^{i}\mathbb 1\{c_j=c\}}\Bigr)\prod_{j=1}^{i}\Bigl(\alpha_j\Bigl(1-\frac{s\,\mathbb 1\{c\in\mathcal U(\{T_1,\dots,T_j\})\}}{\lambda_{\mathcal U(\{T_1,\dots,T_j\})}}\Bigr)\Bigr)^{n_j}.\tag{24}$$
--
--   Theorem 7 gives the sojourn-time distribution of a customer type that is served in order of arrival, for example a type with a single compatible token (Remark 5).
--
--   **Formalization Note** The exponent $\sum_j\mathbb 1\{c_j=c\}$ (printed $\mathbb 1\{c_i=c\}$) and the inner denominator $\lambda_{\mathcal U(\{T_1,\dots,T_j\})}$ (printed $\lambda_c$) are the values forced by substituting $z_c=(\lambda_c-s)/\lambda_c$, $z_d=1$ into (19), which is how the paper proves the theorem; they agree with (22).
--
--   Differences from the source:
--   - encoding: the model of §3 with Conditions 1–2 (types with no compatible token and k = 0 not discussed) → the published hypotheses P.Standing (with T_c ≠ ∅) and KPos (k(T1,…,Tj) > 0 for non-empty token sequences), as in the published Theorem 1; reason: a type with T_c = ∅ is never served, so no stationary law exists and the theorem has no instance there; k > 0 only excludes the cases where α_j and the weights (10) divide by zero
--   - reading: the queue is stable → Summable (weight P): the series in (11) converges; reason: §4.4, p. 9: stability is the convergence of (11); this is the published goal's reading
--   - reading: E and P refer to the stationary system (a stationary distribution of the model with customer types kept) → the statement holds for every Q with IsStationaryLaw P Q: a probability law on customer-level states satisfying the §3 invariant, with summable rows and inflows, in global balance with the forward customer-level rates crate; reason: the performance measures of §5 need the types of the customers, which the descriptor x forgets; uniqueness of the stationary law is not assumed, so the claim is made for each one
--   - encoding: Σ_{i=0}^{K} Σ_{(T1,…,Ti)∈T^i} Σ_{(n1,…,ni)∈N0^i} of the displayed term, with π((0)) given by (11) → HasSum over the published State T (lists of distinct tokens with counts) of the same term, with π((0)) = (Σ_x weight P x)^{-1}; reason: State T enumerates exactly the index set of the triple sum; HasSum asserts that the series converges unconditionally to the left-hand side, so no junk tsum value arises; (Σ_x weight)^{-1} equals (11) because the weight of (0) is 1
--   - encoding: G = P(∩_j {g_j = c_j} | x) → Gcond Q x [c1,…,ci], 0 when Q(desc = x) = 0; reason: as in Theorem 4
--   - reading: S_c, the sojourn time of a type-c customer, in the stationary system → the first-passage LST, from the state just after a tagged type-c arrival to a state drawn from Q, of the tagged customer's departure in the customer-level chain; reason: Poisson arrivals see the stationary law; the jump-path sum is the LST of a first-passage time
--   - reading: type-c customers depart the system in the order of arrival → FifoType P c: in every state reachable from the empty system, a type-c customer has departure rate 0 while an earlier type-c customer is present; reason: a positive departure rate of a later type-c customer would make it overtake with positive probability; the condition is on the dynamics, as the paper's 'instances of the model where' (p. 11)
--   - correction: exponent Σ_{j=1}^{i} 1{c_i = c} → exponent Σ_{j=1}^{i} 1{c_j = c}; reason: the summation index is j; substituting z_c = (λ_c − s)/λ_c, z_d = 1 into ∏_j z_{c_j} of (19), as the proof states, gives Σ_j 1{c_j = c}
--   - correction: inner factor α_j(1 − s 1{c ∈ U({T1,…,Tj})}/λ_c) → α_j(1 − s 1{c ∈ U({T1,…,Tj})}/λ_U({T1,…,Tj})); reason: substituting z_c = (λ_c − s)/λ_c, z_d = 1 into α_j Σ_d θ_{d,j} z_d gives α_j(1 − θ_{c,j} s/λ_c) = α_j(1 − s 1{c∈U}/λ_U), as in (22); with two types sharing all tokens the printed λ_c gives a different value
--   - correction: η(·) any function with η(j) > 0 (Condition 2) → η constant on {1,2,…}: ∀ j ≥ 1, η(j) = η(1); reason: the printed formula is false for non-constant η: one type, one token, λ = 1, s([t]) = 1, η(n) = min(n,4) (stable, Conditions 1–2 hold) at s = 0.7 gives E[e^{-sW}] = 0.8071 by solving the first-passage equations, against 0.7958 from (22); for Theorem 7 the same instance gives 0.5470 against 0.4959 from (24). The proof's distributional Little law (21)/(23) needs the time-till-token (sojourn time) to be unaffected by later arrivals, which fails when the service speed η depends on the total number present; with constant η the two sides agree (0.7941 = 0.7941, 0.5882 = 0.5882 at η ≡ 2). See DISPROOF.md. A tagged customer in service may be alone, so here η must be constant from η(1) on: one token, η = (1,2,2,…), s = 0.7 gives E[e^{-sS}] = 0.4817 against 0.4510 from (24). Excluded cases: every η that is not constant on {1,2,…}
--   - correction: the identity holds for every s with Re s > 0 → for Re s > 0, if the series is summable, it converges to the LST; reason: for large |s| the right-hand side diverges while the LST is finite: one type, one token, λ = 1, s([t]) = 1, η ≡ 2, s = 3 gives terms of modulus π((0))/2 for every n; the identity is asserted wherever the series converges (on the disc |s − λ_c| < λ_c it always does). Excluded cases: the values of s where the printed series diverges, at which the printed equation has no meaning
-- source:
--   Ayesta, Bodas, Dorsman, Verloop, A token-based central queue with order-independent service rates, arXiv:1902.02137v1, p. 11, Theorem 7, Eq. (24); (23) p. 11

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_TokenQueue_ProductForm_Model
import Definitions.Def_TokenQueue_ProductForm_Supplement_CustomerChain

namespace TokenQueue.ProductForm.Supplement

open Finset

/-- **Theorem 7**, p. 11 (corrected: exponent `∑_j 1{c_j = c}` and inner denominator
`λ_{𝒰({T₁,…,T_j})}`, as forced by (19); `η` constant on `{1,2,…}`; the series (24) assumed
convergent). If type-`c` customers depart in the order of arrival, then for complex `s` with
`Re s > 0` the LST `E[e^{−sS_c}]` of the sojourn time of a type-`c` customer arriving to the
stationary system `Q` is the series (24). -/
theorem theorem_7 {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (h1 : Condition1 P) (h2 : Condition2 P) (hk : KPos P)
    (hstab : Summable (weight P)) (Q : CState C T → ℝ) (hQ : IsStationaryLaw P Q)
    (hη : ∀ j, 1 ≤ j → P.eta j = P.eta 1) (c : C) (hfifo : FifoType P c) (s : ℂ)
    (hs : 0 < s.re)
    (hsum : Summable (fun x : State T => (commonFactor P x.1 : ℂ) *
        (∑ cs : Fin x.1.length → C, (Gcond Q x.1 (List.ofFn cs) : ℂ) *
          (((P.lam c : ℂ) - s) / (P.lam c : ℂ)) ^ (univ.filter fun j => cs j = c).card) *
        ∏ j : Fin x.1.length,
          ((alpha P ((toks x.1).take (j + 1)) : ℂ) *
            (1 - s * (if P.tok c ⊆ ((toks x.1).take (j + 1)).toFinset then 1 else 0) /
              (lamU P ((toks x.1).take (j + 1)).toFinset : ℂ))) ^ (x.1.get j).2)) :
    HasSum (fun x : State T => (commonFactor P x.1 : ℂ) *
        (∑ cs : Fin x.1.length → C, (Gcond Q x.1 (List.ofFn cs) : ℂ) *
          (((P.lam c : ℂ) - s) / (P.lam c : ℂ)) ^ (univ.filter fun j => cs j = c).card) *
        ∏ j : Fin x.1.length,
          ((alpha P ((toks x.1).take (j + 1)) : ℂ) *
            (1 - s * (if P.tok c ⊆ ((toks x.1).take (j + 1)).toFinset then 1 else 0) /
              (lamU P ((toks x.1).take (j + 1)).toFinset : ℂ))) ^ (x.1.get j).2)
      (lstS P Q c s) := by sorry

end TokenQueue.ProductForm.Supplement
