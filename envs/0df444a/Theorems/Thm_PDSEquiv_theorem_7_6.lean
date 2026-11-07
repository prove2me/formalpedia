-- Prove2me | Theorems.Thm_PDSEquiv_theorem_7_6
-- name    : PDSEquiv.theorem_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:03:49.960198+00:00
-- url     : https://prove2.me/theorems/31b34b8d-6835-4e36-a151-956865054751
-- title:
--   Theorem 7.6 — search-to-decision: Algorithm 7.1 recovers $C$ with probability $\ge1-e^{-N^\zeta}$ from any oracle satisfying (8)
-- statement:
--   Fix rationals $0<q<p\le1$, $c\in(0,1)$ and $r\in(1-c,1)$, and constants $\gamma\in(0,1]$ and $0<\zeta<1-r$. Let $K\in\{\lfloor N^c\rfloor,N^c\}$, $n=\lfloor N^r\rfloor$ and $\kappa$ an integer with $1\le\kappa\le(1-q)nK/(4N)$. Let $B$ be Algorithm 7.1 with parameters $n,K$: given an $N$-vertex graph it runs in time $\mathrm{poly}(N)$ and makes $N^2+2N$ queries to a randomized oracle $O$ on $n$-vertex graphs. For every sufficiently large $N$ (depending only on $p,q,\gamma,c,r,\zeta$) and every $O$ satisfying (8),
--   $$\Pr_{B,O,G,C}[B^O(G)=C]\ge1-\exp(-N^\zeta)$$
--   under either joint input law:
--
--   1. $(G,C)\sim\widetilde{\mathrm{PDS}}(N,K,p,q)$;
--   2. $(G,C)\sim\mathrm{PDS}(N,K,p,q)$, when $K=\lfloor N^c\rfloor$.
--
--   A distinguisher for the adversarial-$k$ task thus yields strong search in both models.
--
--   Differences from the source:
--   - reading: Let B be Algorithm 7.1 with parameters n, K → ∃ one program per choice of K (⌊N^c⌋ and N^c), chosen before γ, ζ, κ and the oracle, with the printed time, query and success clauses; reason: Algorithm 7.1 uses neither γ nor ζ; its Step 2 draws with an irrational probability when K = N^c, which §4.1 rounds, so the exact algorithm has no exact law on the machine and the theorem is stated for a program meeting the printed guarantees
--   - encoding: makes N² + 2N queries → for N ≥ 2, on every halted branch exactly N² + 2N queries, each an encoded ⌊N^r⌋-vertex graph; for N ≤ 1 only the run bound; reason: Algorithm 7.1 needs 1 ≤ n ≤ N − 1 and K ∈ [1, N − 1], which hold for N ≥ 2
--   - encoding: runs in time poly(N) → ∃ e, log-cost and queries ≤ (N+2)^e on every branch, for every oracle, N and graph; reason: polynomial time uniform in the oracle
--   - encoding: a randomized oracle (distinguisher or search algorithm) on graphs → a family of laws over graphs of every size (DistFamily/SearchFamily), answering a query enc G with [1]/[0] or with the characteristic list of a set, and [] on malformed queries; the hypotheses read it at the stated size only; reason: the black-box oracle of §4.1 with fresh randomness per call; non-uniform oracles are allowed as on the page
--   - reading: randomized polynomial-time algorithm (no machine model named; unit cost for Ber(θ) with O(log N)-bit rational θ, §4.1) → a program of the log-cost RAM PDSEquiv.Machine with exact Ber(a/b) draws for any naturals a ≤ b, charged by bit lengths, halting within (N+2)^c log-cost on every random branch, for every N and every graph; reason: the paper fixes no machine; log-cost RAM time is polynomial Turing-machine time, and allowing every rational θ enlarges both sides of each claim alike while every algorithm of the paper still applies
--   - encoding: input an N-vertex graph G; output a subset T of [N] → input cells enc G = N :: the edge indicators of G in lexicographic pair order (the program computes n and K from N); output the N-bit characteristic list of T; reason: the machine's input and output are lists of naturals; same instances
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Theorem 7.6 and Algorithm 7.1, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_PDSEquiv_Laws
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_PDSEquiv_Assertions
import Definitions.Def_PDSEquiv_Thin

set_option autoImplicit false

namespace PDSEquiv

/-- S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), Theorem 7.6, p.30 (PDF p.32).
Search-to-decision: for each kind of `K`, one program, with exactly `N² + 2N` queries on `n`-vertex
graphs, that recovers the planted set for every oracle satisfying (8).

**Formalization Note.** "Let `B` be Algorithm 7.1" is `∃` program with the printed time, query and
success clauses: `Pf` is for `K = ⌊N^c⌋`, `Pb` for `K = N^c`. Neither depends on `γ`, `ζ`, since
Algorithm 7.1 uses neither. The query count is for `N ≥ 2`, where `1 ≤ n ≤ N − 1` holds because
`0 < r < 1`; at `N ≤ 1` only the bounded run is required. `N₀` depends on `p, q, γ, c, r, ζ` only, and
comes before `κ` and the oracle. -/
theorem theorem_7_6 (p q c r : ℚ) (hq : 0 < q) (hqp : q < p) (hp : p ≤ 1) (hc : 0 < c) (hc1 : c < 1)
    (hr : 1 - c < r) (hr1 : r < 1) :
    ∃ (Pf Pb : Program) (e : ℕ),
      (∀ P ∈ [Pf, Pb], ∀ (O : DistFamily) (N : ℕ) (G : Graph N),
        HaltsWithin P (distOracle O) (enc G) ((N + 2) ^ e) ((N + 2) ^ e) ∧
          QueriesSatisfy P (distOracle O) (enc G) (IsGraphQuery (floorPow N r)) ∧
          OutputsSatisfy P (distOracle O) (enc G) (fun o => ∃ T : Finset (Fin N), o = charList T) ∧
          (2 ≤ N → QueryCountEq P (distOracle O) (enc G) (N ^ 2 + 2 * N))) ∧
      ∀ γ ζ : ℝ, 0 < γ → γ ≤ 1 → 0 < ζ → ζ < 1 - (r : ℝ) →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (κ : ℕ) (O : DistFamily),
          let n := floorPow N r
          let Kf : ℕ := floorPow N c
          let Kb : ℝ := (N : ℝ) ^ (c : ℝ)
          let a : Graph n → ℝ := fun H => distAcc O H
          1 ≤ κ → IsAdversarial p q γ κ a →
          ((κ : ℝ) ≤ (1 - (q : ℝ)) * n * Kf / (4 * N) →
            recProbB N (Kf : ℝ) p q (Behaviour.ofProgram Pf (distOracle O))
                ≥ 1 - Real.exp (-(N : ℝ) ^ ζ) ∧
              recProb N Kf p q (Behaviour.ofProgram Pf (distOracle O))
                ≥ 1 - Real.exp (-(N : ℝ) ^ ζ)) ∧
          ((κ : ℝ) ≤ (1 - (q : ℝ)) * n * Kb / (4 * N) →
            recProbB N Kb p q (Behaviour.ofProgram Pb (distOracle O))
              ≥ 1 - Real.exp (-(N : ℝ) ^ ζ)) := by sorry

end PDSEquiv
