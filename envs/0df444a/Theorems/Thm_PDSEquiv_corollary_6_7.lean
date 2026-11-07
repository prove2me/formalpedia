-- Prove2me | Theorems.Thm_PDSEquiv_corollary_6_7
-- name    : PDSEquiv.corollary_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:03:51.576347+00:00
-- url     : https://prove2.me/theorems/879f606d-fd9e-45b4-b5fa-ce726121d369
-- title:
--   Corollary 6.7 — amplification from search: a weak search oracle gives an adversarial-$k$ distinguisher
-- statement:
--   Fix rationals $0<q<p\le1$, constants $\ell>0$, $a_0>0$, $\tau,r\in(0,1)$ and an integer $d\ge1$. There are constants $\gamma_1>0$ and $N_0$, depending only on $p,q,\ell,a_0,\tau,r,d$, such that for every $N\ge N_0$: let $n=\lfloor N^r\rfloor$ and let $k,\kappa$ be integers with $k\ge N^\ell$, $\kappa\ge N^\tau k$, $\kappa\le n/2$. There is a randomized oracle algorithm $B$, depending only on the fixed parameters, such that for any randomized oracle $S$ that outputs a subset of $[N]$, on input $(H,N,k,\kappa)$ with $H$ a graph on $[n]$, $B^S$ outputs a value in $\{-1,1\}$ and
--   $$\Pr_{B,S,\,H\sim\mathrm{ER}(n,q)}[B^S(H)=1]\le N^{-d}.$$
--   If $\Pr_{S,(G,C)\sim\mathrm{PDS}(N,k,p,q)}[S(G)=C]\ge N^{-a_0}$, then for every integer $\kappa\le j\le n$,
--   $$\Pr_{B,S,\,H\sim\mathrm{PDS}(n,j,p,q)}[B^S(H)=1]\ge\gamma_1.$$
--   The running time and number of queries to $S$ are $\mathrm{poly}(N)$; all queries are on $N$-vertex graphs.
--
--   Differences from the source:
--   - encoding: running time and number of queries poly(N) / N^{O(1)} → ∃ exponent (and constant) chosen before N, the data and the oracle, with log-cost and query count ≤ that bound on every random branch, for every oracle; reason: the meaning of a polynomial bound uniform in the oracle
--   - encoding: a randomized oracle (distinguisher or search algorithm) on graphs → a family of laws over graphs of every size (DistFamily/SearchFamily), answering a query enc G with [1]/[0] or with the characteristic list of a set, and [] on malformed queries; the hypotheses read it at the stated size only; reason: the black-box oracle of §4.1 with fresh randomness per call; non-uniform oracles are allowed as on the page
--   - reading: randomized polynomial-time algorithm (no machine model named; unit cost for Ber(θ) with O(log N)-bit rational θ, §4.1) → a program of the log-cost RAM PDSEquiv.Machine with exact Ber(a/b) draws for any naturals a ≤ b, charged by bit lengths, halting within (N+2)^c log-cost on every random branch, for every N and every graph; reason: the paper fixes no machine; log-cost RAM time is polynomial Turing-machine time, and allowing every rational θ enlarges both sides of each claim alike while every algorithm of the paper still applies
--   - encoding: input (H, N, k, κ) with H a graph on [n]; output a value in {−1, 1} → input cells N :: k :: κ :: enc H; output [1] (value 1) or [0] (value −1); reason: the machine's input and output are lists of naturals; same instances
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Corollary 6.7, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_PDSEquiv_Laws
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_PDSEquiv_Assertions

set_option autoImplicit false

namespace PDSEquiv

/-- S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), Corollary 6.7, p.24 (PDF p.26).
Amplification from search.

**Formalization Note.** The input cells are `N`, `k`, `κ`, then `enc H`. `P`, `γ₁`, `N₀` and the
polynomial bound depend only on the fixed parameters, and come before `N`, `k`, `κ` and the oracle. -/
theorem corollary_6_7 (p q : ℚ) (hq : 0 < q) (hqp : q < p) (hp : p ≤ 1) (ℓ a₀ τ r : ℝ) (hℓ : 0 < ℓ)
    (ha₀ : 0 < a₀) (hτ : 0 < τ) (hτ1 : τ < 1) (hr : 0 < r) (hr1 : r < 1) (d : ℕ) (hd : 1 ≤ d) :
    ∃ (P : Program) (γ₁ : ℝ) (N₀ e : ℕ), 0 < γ₁ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ k κ : ℕ,
      let n := floorPow N r
      (N : ℝ) ^ ℓ ≤ k → (N : ℝ) ^ τ * k ≤ κ → (κ : ℝ) ≤ (n : ℝ) / 2 →
      ∀ S : SearchFamily,
        let acc : Graph n → ℝ := fun H => outMass P (searchOracle S) (N :: k :: κ :: enc H) acceptOut
        (∀ H : Graph n,
          HaltsWithin P (searchOracle S) (N :: k :: κ :: enc H) ((N + 2) ^ e) ((N + 2) ^ e) ∧
            QueriesSatisfy P (searchOracle S) (N :: k :: κ :: enc H) (IsGraphQuery N) ∧
            OutputsSatisfy P (searchOracle S) (N :: k :: κ :: enc H) IsValueOut) ∧
        expect (erMass n q) acc ≤ (N : ℝ) ^ (-(d : ℝ)) ∧
        (recProb N k p q (Kind.behaviour .search S) ≥ (N : ℝ) ^ (-a₀) →
          ∀ j : ℕ, κ ≤ j → j ≤ n → expect (pdsMass n j p q) acc ≥ γ₁) := by sorry

end PDSEquiv
