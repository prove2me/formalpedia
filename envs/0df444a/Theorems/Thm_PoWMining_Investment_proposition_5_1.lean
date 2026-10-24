-- Prove2me | Theorems.Thm_PoWMining_Investment_proposition_5_1
-- name    : PoWMining.Investment.proposition_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:33.985747+00:00
-- url     : https://prove2.me/theorems/7def1a13-4e0c-4b9a-a9a9-0fe397afbc56
-- title:
--   Proposition 5.1, p. 21, corrected — exactly one threshold investment profile is an equilibrium, A(0) always invests and stays active, and entry decreases in K
-- statement:
--   Consider the two-stage game: miners $1,\dots,N$ first choose investments $\beta_i\in[0,1]$, which set their costs-per-hash $c_i(\beta_i)=\tilde c_i-\beta_i(\tilde c_i-\tilde c_0)+\frac{\eta(\tilde c_i-\tilde c_0)}{2}\beta_i^2$, and then play the mining stage at those costs. A miner that was inactive without investment ($i\notin A(0)$) and invests ($\beta_i>0$) pays the fixed cost $K$. Assume the standing assumptions ($N\ge2$, $R>0$, $\gamma\ge0$, $\eta\ge0$, $K>0$, $\tilde c_1\le\dots\le\tilde c_N$, $0<\tilde c_0<\tilde c_i$ for all $i$), let $h^*$ be any mining-equilibrium selection, and assume $K$ is generic. Write $\bar\beta=\min\{1/\eta,1\}$ and let $\beta^{(n)}$ be the threshold profile (5.1):
--
--   $$
--   \beta^{(n)}_i=\begin{cases}\bar\beta, & 1\le i\le n,\\ 0, & n<i\le N.\end{cases}
--   $$
--
--   Then:
--
--   1. There is exactly one $n$ with $2\le n\le N$ such that $\beta^{(n)}$ is an equilibrium investment. For such $n$, exactly $n$ miners are active at $\beta^{(n)}$, and $A(0)\subseteq A(\beta^{(n)})$.
--   2. At every equilibrium investment $\beta^*$, every miner of $A(0)$ invests $\bar\beta$ and is active: $A(0)\subseteq A(\beta^*)$.
--   3. The number $n$ of active miners is decreasing in $K$: if $K\le K'$ (both generic, all other parameters equal) and $\beta^{(n)}$, $\beta^{(n')}$ are the threshold equilibria for $K$ and $K'$, then $n'\le n$.
--
--   Investment thus keeps every incumbent miner active, entry happens in order of initial efficiency, and a higher entry cost admits fewer miners.
--
--   **Formalization Note** The printed Proposition 5.1 claims a *unique* equilibrium investment, and that claim is **false**. Take $\tilde c=(1.074,1.419,2.914,2.923)$, $\tilde c_0=0.31$, $\eta=0.5$, $\gamma=0.5$, $R=1$ and any $K\in(0.0168,0.0308)$. Then $A(0)=\{1,2\}$ and there is room for exactly one entrant, so both $(1,1,1,0)$ and $(1,1,0,1)$ are equilibrium investments. The same instance refutes the claim on p. 45 that a miner cannot invest while a cheaper miner does not. This statement therefore keeps every true printed conclusion: the form (5.1), $A(0)\subseteq A(\beta^*)$ (the paper's "$A(\beta^*_i)$"), and $n$ decreasing in $K$, read weakly as in footnote 12. Uniqueness is replaced by uniqueness within the family (5.1) (part 1) together with what every equilibrium satisfies (part 2). Three hypotheses are added, each necessary. (i) $\tilde c_0<\tilde c_i$ for all $i$ (the paper allows $\le$; at equality $c_i$ is constant in $\beta_i$ and every $\beta_i$ is a best response). (ii) $\tilde c_0>0$ (no sign is stated). (iii) $K$ generic: for each $i\notin A(0)$, miner $i$'s gross profit at $\beta^{(i)}$ differs from $K$ (at equality two threshold profiles are equilibria). The selection $h^*$ is a hypothesis; Proposition 4.1 makes it unique. Lean indices are 0-based, and the comparison in $K$ uses the same selection, since the mining stage does not involve $K$.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 21, Proposition 5.1 (corrected: printed uniqueness is false); pp. 44–46, proof of Proposition 5.1

import Mathlib
import Definitions.Def_PoWMining_Investment_Model

namespace PoWMining.Investment

/-- Proposition 5.1 (p. 21), corrected (paper.md slip 16; the printed uniqueness among all
investment profiles is false). Under the standing assumptions and the genericity of `K`, for
every mining-equilibrium selection `hstar`:
(a) exactly one threshold profile (5.1) with `2 ≤ n ≤ N` is an equilibrium investment, and at
such a profile exactly `n` miners are active and `A(0) ⊆ A(β*)`;
(b) at every equilibrium investment, every miner of `A(0)` invests `min{1/η, 1}` and is active;
(c) the threshold `n` is nonincreasing in the fixed cost `K`. -/
theorem proposition_5_1 {N : ℕ} (P : InvParams N) (hP : P.Standing)
    (hstar : (Fin N → ℝ) → Fin N → ℝ) (hsel : IsSelection P hstar)
    (hgen : Generic P hstar) :
    (∃! n : ℕ, 2 ≤ n ∧ n ≤ N ∧ IsInvEq P hstar (betaK P n)) ∧
    (∀ n : ℕ, 2 ≤ n → n ≤ N → IsInvEq P hstar (betaK P n) →
      (active hstar (betaK P n)).card = n ∧ A0 hstar ⊆ active hstar (betaK P n)) ∧
    (∀ β : Fin N → ℝ, IsInvEq P hstar β →
      A0 hstar ⊆ active hstar β ∧ ∀ i ∈ A0 hstar, β i = betaBar P) ∧
    (∀ K' : ℝ, P.K ≤ K' → Generic { P with K := K' } hstar →
      ∀ n n' : ℕ, 2 ≤ n → n ≤ N → 2 ≤ n' → n' ≤ N →
        IsInvEq P hstar (betaK P n) → IsInvEq { P with K := K' } hstar (betaK P n') →
        n' ≤ n) := by sorry

end PoWMining.Investment
