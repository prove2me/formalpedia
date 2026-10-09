-- Prove2me | Theorems.Thm_RubinsteinNash_WeakNash_trim_is_ws_weakNash
-- name    : RubinsteinNash.WeakNash.trim_is_ws_weakNash
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:30.264235+00:00
-- url     : https://prove2.me/theorems/f015ae02-2f1f-44d9-959e-2e34fd4360ef
-- title:
--   Proof of Lemma 8.1, p. 51 — the trimmed profile is a (kε + 2/(k − 1), δ)-Well-Supported WeakNash
-- statement:
--   Consider a complete bipartite polymatrix game with sides $V_A$, $V_B$, $n_A=|V_A|$, $n_B=|V_B|$, in which every subgame payoff of a vertex in $V_A$ lies in $[0,1/n_B]$ and every subgame payoff of a vertex in $V_B$ lies in $[0,1/n_A]$. Let $\epsilon>0$, $k>1$, and let $x$ be an $(\epsilon,\delta)$-WeakNash of the game. Let $\hat x$ be the trimmed profile (every $\epsilon$-optimal player $v$ keeps only the actions within $\epsilon k$ of $U^v_{\max}(x^{-v})$ and renormalises; every other player keeps $x^v$). Then
--   $$\hat x\ \text{is a}\ \Bigl(k\epsilon+\frac{2}{k-1},\ \delta\Bigr)\text{-Well-Supported WeakNash}.$$
--
--   This is the general-$k$ form of Lemma 8.1; the lemma follows by choosing $k=1+1/\sqrt\epsilon$.
--
--   **Formalization Note.** The constant $k\epsilon+2/(k-1)$ is the one the page states. The displayed chain that follows it on the page ends with $-\epsilon k-4/(k-1)$; the stated $2/(k-1)$ is nevertheless true, because $\hat x^u-x^u$ sums to $0$ for every player, so a subgame payoff with range $[0,c]$ changes by at most $\tfrac c2\|\hat x^u-x^u\|_1$. The polynomial-time construction is the explicit profile $\hat x$ computed from $x$.
-- source:
--   Rubinstein, arXiv:1606.04550 (version dated August 26, 2016), proof of Lemma 8.1, §8.1, p. 51 ('It follows that x̂ is a (kϵ + 2/(k−1), δ)-Well-Supported-WeakNash')

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_DGPNash_WellSupported_Equilibria
import Definitions.Def_RubinsteinNash_WeakNash_ApproxEquilibria
import Definitions.Def_RubinsteinNash_WeakNash_Polymatrix

namespace RubinsteinNash.WeakNash

theorem trim_is_ws_weakNash {VA VB : Type*} [Fintype VA] [DecidableEq VA]
    [Fintype VB] [DecidableEq VB]
    {S : VA ⊕ VB → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (PA : (v : VA) → (w : VB) → S (Sum.inl v) → S (Sum.inr w) → ℝ)
    (PB : (w : VB) → (v : VA) → S (Sum.inr w) → S (Sum.inl v) → ℝ)
    (hPA : ∀ v w a b, 0 ≤ PA v w a b ∧ PA v w a b ≤ 1 / (Fintype.card VB : ℝ))
    (hPB : ∀ w v b a, 0 ≤ PB w v b a ∧ PB w v b a ≤ 1 / (Fintype.card VA : ℝ))
    (x : ∀ i, S i → ℝ) (ε δ k : ℝ) (hε : 0 < ε) (hk : 1 < k)
    (hx : IsWeakNash (bipartitePolymatrixPayoff PA PB) x ε δ) :
    IsWellSupportedWeakNash (bipartitePolymatrixPayoff PA PB)
      (weakTrim (bipartitePolymatrixPayoff PA PB) x ε k) (k * ε + 2 / (k - 1)) δ := by sorry

end RubinsteinNash.WeakNash
