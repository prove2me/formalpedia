-- Prove2me | Theorems.Thm_PDSEquiv_proposition_6_6
-- name    : PDSEquiv.proposition_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:10.159646+00:00
-- url     : https://prove2.me/theorems/30c67303-417f-48ae-a551-bbb99e9e18ba
-- title:
--   Proposition 6.6 — amplification from decision: a high vertex-degree planted mean $\ge N^{-2}$ gives an adversarial-$k$ distinguisher
-- statement:
--   Fix rationals $0<q<p\le1$, constants $r,\tau\in(0,1)$ and an integer $d\ge1$. Let $D\ge2$ be the least integer with $(1-r)(D+1)\ge2d+11$. There are constants $\gamma>0$ and $N_0$, depending only on these parameters, such that for $N\ge N_0$ and integers $k,\kappa$ with
--   $$n=\lfloor N^r\rfloor,\qquad k\ge1,\qquad N^\tau k\le\kappa\le n/2,$$
--   there is a randomized oracle algorithm $B$, depending only on $p,q,r,\tau,d$, with this guarantee. Let $O$ be any randomized $\{-1,1\}$-valued oracle on graphs on $[N]$ and $f(G)=\mathbb E_O[O(G)]$. On input $(G,N,k,\kappa)$ with $G$ a graph on $[n]$, $B^O$ outputs a value in $\{-1,1\}$ and
--
--   1. $\Pr_{B,O,\,G\sim\mathrm{ER}(n,q)}[B^O(G)=1]\le N^{-d}$;
--   2. if $\bigl|\mathbb E_{Y\sim\mathrm{PDS}(N,k,p,q)}[f^{>D}(Y)]\bigr|\ge N^{-2}$, then $\Pr_{B,O,\,G\sim\mathrm{PDS}(n,j,p,q)}[B^O(G)=1]\ge\gamma$ for every integer $\kappa\le j\le n$.
--
--   The running time and number of queries to $O$ are $N^{O(1)}$, with exponents depending only on $q,r,d$; all queries are on $N$-vertex graphs.
--
--   **Formalization Note** The input cells are $N,k,\kappa$ followed by the encoding of $G$, which carries $n$; $r$ and $\tau$ are real, as printed, and the program never computes $N^r$.
--
--   Differences from the source:
--   - encoding: running time and number of queries N^{O(1)}, exponents depending only on q, r, d → ∃ e chosen after q, r, d and before p, τ; ∃ C after all parameters; log-cost and queries ≤ C·(N+2)^e on every branch, every oracle; reason: the page's dependence of the exponent, with the constant factor allowed by O(1)
--   - encoding: a randomized oracle (distinguisher or search algorithm) on graphs → a family of laws over graphs of every size (DistFamily/SearchFamily), answering a query enc G with [1]/[0] or with the characteristic list of a set, and [] on malformed queries; the hypotheses read it at the stated size only; reason: the black-box oracle of §4.1 with fresh randomness per call; non-uniform oracles are allowed as on the page
--   - reading: randomized polynomial-time algorithm (no machine model named; unit cost for Ber(θ) with O(log N)-bit rational θ, §4.1) → a program of the log-cost RAM PDSEquiv.Machine with exact Ber(a/b) draws for any naturals a ≤ b, charged by bit lengths, halting within (N+2)^c log-cost on every random branch, for every N and every graph; reason: the paper fixes no machine; log-cost RAM time is polynomial Turing-machine time, and allowing every rational θ enlarges both sides of each claim alike while every algorithm of the paper still applies
--   - encoding: input (G, N, k, κ) with G a graph on [n]; output a value in {−1, 1} → input cells N :: k :: κ :: enc G; output [1] (value 1) or [0] (value −1); reason: the machine's input and output are lists of naturals; same instances
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Proposition 6.6, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_PDSEquiv_Laws
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_PDSEquiv_Assertions
import Definitions.Def_PDSEquiv_Fourier

set_option autoImplicit false

namespace PDSEquiv

/-- S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), Proposition 6.6, p.23 (PDF p.25).
Amplification from decision.

**Formalization Note.** `r` and `τ` are real, as printed: the input carries `n` in the encoding of its
graph, so the program never computes `N^r`. The input cells are `N`, `k`, `κ`, then `enc H`. The
exponent `e` depends only on `q`, `r`, `d`, so it comes before `p` and `τ`; `P`, `γ`, `N₀`, `C` depend
on all of them; everything comes before `N`, `k`, `κ` and the oracle. -/
theorem proposition_6_6 (q : ℚ) (hq : 0 < q) (hq1 : q < 1) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (d : ℕ)
    (hd : 1 ≤ d) :
    ∃ e : ℕ, ∀ p : ℚ, q < p → p ≤ 1 → ∀ τ : ℝ, 0 < τ → τ < 1 →
      ∃ (P : Program) (γ : ℝ) (N₀ C : ℕ), 0 < γ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ k κ : ℕ,
        let n := floorPow N r
        1 ≤ k → (N : ℝ) ^ τ * k ≤ κ → (κ : ℝ) ≤ (n : ℝ) / 2 →
        ∀ O : DistFamily,
          let f : Graph N → ℝ := signedMean (fun G => distAcc O G)
          let acc : Graph n → ℝ := fun H => outMass P (distOracle O) (N :: k :: κ :: enc H) acceptOut
          (∀ H : Graph n,
            HaltsWithin P (distOracle O) (N :: k :: κ :: enc H) (C * (N + 2) ^ e) (C * (N + 2) ^ e) ∧
              QueriesSatisfy P (distOracle O) (N :: k :: κ :: enc H) (IsGraphQuery N) ∧
              OutputsSatisfy P (distOracle O) (N :: k :: κ :: enc H) IsValueOut) ∧
          expect (erMass n q) acc ≤ (N : ℝ) ^ (-(d : ℝ)) ∧
          (|expect (pdsMass N k p q) (highPart (q : ℝ) (leastD r d) f)| ≥ (N : ℝ) ^ (-(2 : ℝ)) →
            ∀ j : ℕ, κ ≤ j → j ≤ n → expect (pdsMass n j p q) acc ≥ γ) := by sorry

end PDSEquiv
