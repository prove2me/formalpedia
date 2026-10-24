-- Prove2me | Theorems.Thm_PoWMining_Equilibrium_proposition_4_4
-- name    : PoWMining.Equilibrium.proposition_4_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:10.374876+00:00
-- url     : https://prove2.me/theorems/7a4f22a0-6e86-44b0-9903-b7cbf0dabeb3
-- title:
--   Proposition 4.4, p. 14 — the number of active miners is the largest $2\le n\le N$ with $c_n<(c^{(n)}+R\gamma/c_n)/(n-1)$, increasing in R and γ
-- statement:
--   Consider the mining game with $N\ge 2$ miners, reward $R>0$, capacity parameter $\gamma\ge 0$ and sorted positive costs-per-hash $0<c_1\le\cdots\le c_N$, in which miner $i$ choosing $h_i\ge 0$ earns $(h_i/H)R-c_ih_i-(\gamma/2)h_i^2$ if $H=\sum_jh_j>0$ and $0$ if $H=0$. Write $c^{(n)}=c_1+\cdots+c_n$.
--
--   1. An equilibrium hash rate profile exists.
--   2. In every equilibrium hash rate profile, the number of active miners is the largest $2\le n\le N$ such that
--   $$c_n<\frac{c^{(n)}+R\gamma/c_n}{n-1}.$$
--   3. This number is increasing in $R$ and $\gamma$: if $(R',\gamma')$ is a second parameter pair with the same costs, $R\le R'$ and $\gamma\le\gamma'$, then the number of active miners in an equilibrium for $(R,\gamma)$ is at most the number in an equilibrium for $(R',\gamma')$.
--
--   The proposition determines the set of active miners from the model parameters alone. A larger reward or a tighter capacity constraint (larger $\gamma$) lets weakly more miners participate; with $\gamma=0$ the condition does not involve $R$ at all.
--
--   **Formalization Note** The paper's miner $n$ is Lean index $n-1$, and $c^{(n)}$ sums Lean indices $<n$. The participation condition is the predicate `partCond P n` on natural numbers. "Largest" is `IsGreatest` of the set $\{n:2\le n\le N,\ \text{condition at } n\}$. Existence of an equilibrium is included so that the statements about every equilibrium are not vacuous; uniqueness is Proposition 4.1. "Increasing" is weak (footnote 12) and is stated as one joint comparison in $(R,\gamma)$, both parameter records satisfying the standing assumptions.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 14, Proposition 4.4

import Mathlib
import Definitions.Def_PoWMining_Equilibrium_Setting

namespace PoWMining.Equilibrium

/-- Proposition 4.4, p. 14: an equilibrium exists, the number of active miners in (every)
equilibrium is the largest `2 ≤ n ≤ N` with `c_n < (c⁽ⁿ⁾ + Rγ/c_n)/(n − 1)`, and this number is
increasing (weakly) in `R` and `γ`. -/
theorem proposition_4_4 {N : ℕ} (P : Params N) (hP : P.Standing) :
    (∃ h : Fin N → ℝ, IsMiningEq P h) ∧
      (∀ h : Fin N → ℝ, IsMiningEq P h →
        IsGreatest {k : ℕ | 2 ≤ k ∧ k ≤ N ∧ partCond P k} (activeCount h)) ∧
      (∀ P' : Params N, P'.Standing → P'.c = P.c → P.R ≤ P'.R → P.γ ≤ P'.γ →
        ∀ h h' : Fin N → ℝ, IsMiningEq P h → IsMiningEq P' h' →
          activeCount h ≤ activeCount h') := by sorry

end PoWMining.Equilibrium
