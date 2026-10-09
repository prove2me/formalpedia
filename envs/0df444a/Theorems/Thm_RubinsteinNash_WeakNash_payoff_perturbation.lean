-- Prove2me | Theorems.Thm_RubinsteinNash_WeakNash_payoff_perturbation
-- name    : RubinsteinNash.WeakNash.payoff_perturbation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:50:26.514486+00:00
-- url     : https://prove2.me/theorems/830eab15-0c6d-4a5a-9ec9-bb4677d712b2
-- title:
--   Proof of Lemma 8.1, p. 51 — in the bipartite polymatrix game, trimming changes every U^v_s by at most 2/(k − 1)
-- statement:
--   Consider a complete bipartite polymatrix game with sides $V_A$, $V_B$, $n_A=|V_A|$, $n_B=|V_B|$, in which the subgame payoff $U^{v,w}$ of a vertex $v\in V_A$ against $w\in V_B$ lies in $[0,1/n_B]$ and the subgame payoff $U^{w,v}$ of $w\in V_B$ against $v\in V_A$ lies in $[0,1/n_A]$. Let $x$ be a mixed-strategy profile, $\epsilon>0$, $k>1$, and let $\hat x$ be the trimmed profile of the proof of Lemma 8.1. Then for every vertex $v\in V_A\cup V_B$ and every action $s\in S^v$,
--   $$\bigl|U^v_s(x^{-v})-U^v_s(\hat x^{-v})\bigr|\ \le\ \frac{2}{k-1}.$$
--
--   Together with the choice of $\hat x$, this bounds how far the best responses can move when the profile is trimmed.
--
--   **Formalization Note.** The page writes the argument for $v\in V_A$ and says that the one for $V_B$ "follows with minor modifications"; the statement covers both sides. The payoff range of a vertex on side $A$ is $[0,1/n_B]$ (it has $n_B$ neighbours) and on side $B$ is $[0,1/n_A]$, as the proof uses. If one side is empty, $1/0=0$ in Lean forces the other side's payoffs to be $0$, and the statement is then trivial.
-- source:
--   Rubinstein, arXiv:1606.04550 (version dated August 26, 2016), proof of Lemma 8.1, §8.1, p. 51, first display

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_DGPNash_WellSupported_Equilibria
import Definitions.Def_RubinsteinNash_WeakNash_ApproxEquilibria
import Definitions.Def_RubinsteinNash_WeakNash_Polymatrix

namespace RubinsteinNash.WeakNash

theorem payoff_perturbation {VA VB : Type*} [Fintype VA] [DecidableEq VA]
    [Fintype VB] [DecidableEq VB]
    {S : VA ⊕ VB → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (PA : (v : VA) → (w : VB) → S (Sum.inl v) → S (Sum.inr w) → ℝ)
    (PB : (w : VB) → (v : VA) → S (Sum.inr w) → S (Sum.inl v) → ℝ)
    (hPA : ∀ v w a b, 0 ≤ PA v w a b ∧ PA v w a b ≤ 1 / (Fintype.card VB : ℝ))
    (hPB : ∀ w v b a, 0 ≤ PB w v b a ∧ PB w v b a ≤ 1 / (Fintype.card VA : ℝ))
    (x : ∀ i, S i → ℝ) (hx : AGT.IsMixedProfile x)
    (ε k : ℝ) (hε : 0 < ε) (hk : 1 < k) :
    ∀ (p : VA ⊕ VB) (s : S p),
      |DGPNash.NashMap.purePayoff (bipartitePolymatrixPayoff PA PB) x p s -
        DGPNash.NashMap.purePayoff (bipartitePolymatrixPayoff PA PB)
          (weakTrim (bipartitePolymatrixPayoff PA PB) x ε k) p s| ≤ 2 / (k - 1) := by sorry

end RubinsteinNash.WeakNash
