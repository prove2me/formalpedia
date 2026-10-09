-- Prove2me | Theorems.Thm_RubinsteinNash_WeakNash_lemma_8_1
-- name    : RubinsteinNash.WeakNash.lemma_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:49:59.066185+00:00
-- url     : https://prove2.me/theorems/578e4130-d54b-40b5-9850-966d4f419dbe
-- title:
--   Lemma 8.1, p. 50 — trimming an (ε, δ)-WeakNash of a bipartite polymatrix game gives a (√ε(√ε + 5), δ)-Well-Supported WeakNash
-- statement:
--   Consider a complete bipartite polymatrix game: the players are split into two sides $V_A$ and $V_B$, with $n_A=|V_A|$ and $n_B=|V_B|$, and every $v\in V_A$ and $w\in V_B$ play a bimatrix subgame in which $v$'s payoffs lie in $[0,1/n_B]$ and $w$'s payoffs lie in $[0,1/n_A]$; each player's utility is the sum of its subgame payoffs. Let $\epsilon>0$ and let $x$ be an $(\epsilon,\delta)$-WeakNash of the game: for at least a $(1-\delta)$-fraction of the players, the mixed strategy $x^v$ is an $\epsilon$-best mixed response to $x^{-v}$.
--
--   Put $k=1+1/\sqrt\epsilon$ and let $\hat x$ be the trimmed profile: for every player $v$ who plays $\epsilon$-optimally in $x$,
--   $$\hat x^v_s=\begin{cases}\dfrac{x^v_s}{1-z^v}, & U^v_s(x^{-v})\ge U^v_{\max}(x^{-v})-\epsilon k,\\[4pt] 0, & \text{otherwise,}\end{cases}$$
--   where $z^v$ is the probability $x^v$ puts on actions more than $\epsilon k$ below the optimum, and every other player keeps $\hat x^v=x^v$. Then
--   $$\hat x\ \text{is a}\ \bigl(\sqrt\epsilon\cdot(\sqrt\epsilon+5),\ \delta\bigr)\text{-Well-Supported WeakNash}.$$
--
--   The lemma converts the (mixed-response) WeakNash notion, for which the paper proves hardness, into the support notion needed by the reduction to two-player games in Section 8.2, losing only a square-root in the approximation.
--
--   **Formalization Note.** The paper says the well-supported WeakNash "can be constructed in polynomial time"; the running-time clause is not formalized. What is stated is that the specific profile $\hat x$ computed from $x$ by the proof's explicit formula has the property; the bare existence of some well-supported WeakNash would follow from Nash's theorem without using $x$. The hypothesis $\epsilon>0$ is added: $k=1+1/\sqrt\epsilon$ needs it. The payoff range $[0,1/n_B]$ is that of the vertices of $V_A$ (which have $n_B$ neighbours) and $[0,1/n_A]$ that of $V_B$. Players who are not $\epsilon$-optimal in $x$ keep their strategy in $\hat x$, since the page defines $\hat x^v$ only for the $\epsilon$-optimal ones.
-- source:
--   Rubinstein, arXiv:1606.04550 (version dated August 26, 2016), Lemma 8.1, §8.1, p. 50 (proof pp. 50–51)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_DGPNash_WellSupported_Equilibria
import Definitions.Def_RubinsteinNash_WeakNash_ApproxEquilibria
import Definitions.Def_RubinsteinNash_WeakNash_Polymatrix

namespace RubinsteinNash.WeakNash

theorem lemma_8_1 {VA VB : Type*} [Fintype VA] [DecidableEq VA]
    [Fintype VB] [DecidableEq VB]
    {S : VA ⊕ VB → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (PA : (v : VA) → (w : VB) → S (Sum.inl v) → S (Sum.inr w) → ℝ)
    (PB : (w : VB) → (v : VA) → S (Sum.inr w) → S (Sum.inl v) → ℝ)
    (hPA : ∀ v w a b, 0 ≤ PA v w a b ∧ PA v w a b ≤ 1 / (Fintype.card VB : ℝ))
    (hPB : ∀ w v b a, 0 ≤ PB w v b a ∧ PB w v b a ≤ 1 / (Fintype.card VA : ℝ))
    (x : ∀ i, S i → ℝ) (ε δ : ℝ) (hε : 0 < ε)
    (hx : IsWeakNash (bipartitePolymatrixPayoff PA PB) x ε δ) :
    IsWellSupportedWeakNash (bipartitePolymatrixPayoff PA PB)
      (weakTrim (bipartitePolymatrixPayoff PA PB) x ε (1 + 1 / Real.sqrt ε))
      (Real.sqrt ε * (Real.sqrt ε + 5)) δ := by sorry

end RubinsteinNash.WeakNash
