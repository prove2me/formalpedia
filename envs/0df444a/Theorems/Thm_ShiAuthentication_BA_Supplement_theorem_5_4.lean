-- Prove2me | Theorems.Thm_ShiAuthentication_BA_Supplement_theorem_5_4
-- name    : ShiAuthentication.BA.Supplement.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:26:32.588598+00:00
-- url     : https://prove2.me/theorems/89f9c77f-1d6e-4da4-a40c-443242a76f92
-- title:
--   Theorem 5.4 — broadcast lower bound near the honest-majority threshold
-- statement:
--   Let $S$ be the designated sender, $R=P\setminus\{S\}$ the receivers, and $E_R=E(G)\cap(R\times R)$ the authentication edges between receivers. There are constants $c>0$ and $\Lambda_0>1$ with the following property. Let $2t<n\le 3t$, put $r=n-2t$ and $\Lambda=\ln(n/r)$. If $\Lambda\ge\Lambda_0$ and $\mathrm{BB}(G,S,t)$ is feasible on the public authentication graph $G$, then
--   $$|E_R|\ \ge\ c\,\frac{n\Lambda^2}{\ln\Lambda}.$$
--   In particular, at $n=2t+1$ every feasible graph has $|E_R|=\Omega\big(n\ln^2 n/\ln\ln n\big)$: there are $c'>0$ and $N_0$ such that every feasible graph with $n=2t+1\ge N_0$ has $|E_R|\ge c'\,n\ln^2 n/\ln\ln n$.
--
--   The theorem shows that broadcast needs superlinearly many authentication edges among the receivers when $n-2t=o(n)$, in contrast with the linear cost for a fixed fault fraction below $1/2$.
--
--   Differences from the source:
--   - encoding: BB(G, S, t) feasible → BBPossible .publicGraph t G S; reason: Definition 3.1 in the model of §3.1, where the authentication graph G is public
--   - encoding: at n = 2t + 1, |E_R| = Ω(n ln² n / ln ln n) → ∃ c' > 0, ∃ N₀, ∀ n t G S with n = 2t + 1 ≥ N₀ and BB feasible, c' n ln² n / ln ln n ≤ |E_R|; reason: Ω is asymptotic in n; the threshold excludes small n, where ln ln n ≤ 0
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Theorem 5.4, p. 26; proof pp. 31–32

import Definitions.Def_ShiAuthentication_BA_Supplement_Complexity

set_option autoImplicit false

namespace ShiAuthentication.BA.Supplement

/-- **Theorem 5.4 (Broadcast lower bound)**, p. 26. There are constants `c > 0` and `Λ₀ > 1` such
that: if `2t < n ≤ 3t`, `r = n − 2t`, `Λ = ln(n/r) ≥ Λ₀` and `BB(G, S, t)` is feasible (public
authentication graph), then the number `|E_R|` of authentication edges between receivers
(`R = P \ {S}`) satisfies `|E_R| ≥ c n Λ² / ln Λ`. In particular, at `n = 2t + 1`, every
feasible graph has `|E_R| = Ω(n ln² n / ln ln n)`: some `c' > 0` and threshold `N₀` give
`|E_R| ≥ c' n ln² n / ln ln n` whenever `n = 2t + 1 ≥ N₀`. -/
theorem theorem_5_4 :
    (∃ c Λ₀ : ℝ, 0 < c ∧ 1 < Λ₀ ∧ ∀ (n t r : ℕ) (G : AuthGraph n) (S : Fin n),
      2 * t < n → n ≤ 3 * t → r = n - 2 * t → Λ₀ ≤ Real.log ((n : ℝ) / r) →
      BBPossible .publicGraph t G S →
      c * n * Real.log ((n : ℝ) / r) ^ 2 / Real.log (Real.log ((n : ℝ) / r)) ≤
        receiverEdgeCount G S) ∧
    (∃ c' : ℝ, 0 < c' ∧ ∃ N₀ : ℕ, ∀ (n t : ℕ) (G : AuthGraph n) (S : Fin n),
      n = 2 * t + 1 → N₀ ≤ n → BBPossible .publicGraph t G S →
      c' * n * Real.log n ^ 2 / Real.log (Real.log n) ≤ receiverEdgeCount G S) := by sorry

end ShiAuthentication.BA.Supplement
