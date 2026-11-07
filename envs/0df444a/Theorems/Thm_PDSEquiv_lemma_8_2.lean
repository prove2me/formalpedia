-- Prove2me | Theorems.Thm_PDSEquiv_lemma_8_2
-- name    : PDSEquiv.lemma_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:05:11.985115+00:00
-- url     : https://prove2.me/theorems/e443d41e-d56c-467d-a8d7-cdc9171e8843
-- title:
--   Lemma 8.2 — decision from an unknown planted-set size: distinguishers $B$ and (AD) distinguishers $D$ in cases (A) and (B)
-- statement:
--   Fix rationals $0<\ell<u<c<1/2$ and $0<q<p\le1$, constants $0<\zeta<c-u$ and $a_0>0$, a rational $r\in(1+u-c,1-\zeta)$, and set $K_N=\lfloor N^c\rfloor$, $n=\lfloor N^r\rfloor$, $\kappa=\lfloor\frac{1-q}{64}\cdot\frac{nK_N}{N}\rfloor$ (12). There are an integer $D_0\ge2$ depending only on $u,c,r$ and constants $\gamma>0$, $N_1$ depending only on the fixed parameters such that, in each case below, there is a randomized polynomial-time oracle distinguisher $B$, depending only on the fixed parameters, for every oracle $O$ receiving $(G,k)$ with $G$ a graph on $[N]$, $k\in[N]$:
--
--   1. **(A)** $O=A$ is a distinguisher, $f_{N,k}(G)=\mathbb E_A[A(G,k)]$; the input condition at size $N$ is that some integer $k\in[2,N^u]$ has $\bigl|\mathbb E_{\mathrm{PDS}(N,k,p,q)}[(I-\Pi_{D_0})f_{N,k}]\bigr|\ge N^{-2}$.
--   2. **(B)** $O=S$ is a search algorithm; the input condition is that some integer $k\in[N^\ell,N^u]$ has $\Pr_{S,(G,C)\sim\mathrm{PDS}(N,k,p,q)}[S(G,k)=C]\ge N^{-a_0}$.
--
--   $B^O(H,N)$ takes a graph $H$ on $[n]$ and $N$. For every $N\ge N_1$, regardless of the input condition, $\Pr_{H\sim\mathrm{ER}(n,q)}[B^O(H,N)=1]\le N^{-1}$; if the condition holds at $N\ge N_1$, then $\Pr_{H\sim\mathrm{PDS}(n,j,p,q)}[B^O(H,N)=1]\ge\gamma$ for all $\kappa\le j\le n$. $B$ makes $\mathrm{poly}(N)$ queries, each of the form $(G,k)$. Moreover, $B$ converts into a randomized polynomial-time oracle distinguisher $D$ with the same query bounds that takes only a graph $G$ on $[N]$, and for every $N\ge N_1$ satisfying the condition meets the (AD) acceptance bounds with exponent $c$ and constant $\gamma/2$.
--
--   This removes the need to know the planted-set size at which the weak algorithm succeeds.
--
--   Differences from the source:
--   - encoding: The construction of B may differ between the two cases; D converted from B → four programs (B and D for case (A), B and D for case (B)) under one D₀, γ, N₁ and one polynomial exponent; reason: the page's two cases and the conversion
--   - encoding: randomized polynomial-time; poly(N) queries → ∃ e, log-cost and queries ≤ (N+2)^e on every branch for every N, input graph and oracle; reason: polynomial time uniform in the oracle
--   - encoding: rationals ℓ < u < c, q < p as fixed in §8 → D₀ quantified after u, c, r only; q, p, ℓ, ζ, a₀ after it; reason: D₀ depends only on u, c, r as printed
--   - encoding: a randomized oracle (distinguisher or search algorithm) on graphs → a family of laws over graphs of every size (DistFamily/SearchFamily), answering a query enc G with [1]/[0] or with the characteristic list of a set, and [] on malformed queries; the hypotheses read it at the stated size only; reason: the black-box oracle of §4.1 with fresh randomness per call; non-uniform oracles are allowed as on the page
--   - reading: randomized polynomial-time algorithm (no machine model named; unit cost for Ber(θ) with O(log N)-bit rational θ, §4.1) → a program of the log-cost RAM PDSEquiv.Machine with exact Ber(a/b) draws for any naturals a ≤ b, charged by bit lengths, halting within (N+2)^c log-cost on every random branch, for every N and every graph; reason: the paper fixes no machine; log-cost RAM time is polynomial Turing-machine time, and allowing every rational θ enlarges both sides of each claim alike while every algorithm of the paper still applies
--   - encoding: B^O(H, N) with H a graph on [n]; D^O(G); oracle queries (G, k) with k ∈ [N]; outputs in {−1, 1} → B's input cells N :: enc H, D's input cells enc G; a query is the list N :: k :: edge bits of G with 1 ≤ k ≤ N; output [1] (value 1) or [0] (value −1); reason: the machine's input, queries and output are lists of naturals; B needs N as input since |V(H)| does not determine it, as the page notes
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Lemma 8.2 and (12), p.34 (PDF p.36)

import Mathlib
import Definitions.Def_PDSEquiv_Laws
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_PDSEquiv_Assertions
import Definitions.Def_PDSEquiv_Fourier
import Definitions.Def_PDSEquiv_UnknownSize

set_option autoImplicit false

namespace PDSEquiv

/-- S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), Lemma 8.2, p.34 (PDF p.36).
Decision from an unknown planted-set size.

**Formalization Note.** `D₀` depends only on `u, c, r`, so it comes before the other parameters. `γ`,
`N₁`, the four programs and the polynomial bound depend on the fixed parameters and come before the
oracle. `BA`, `DA` are case (A), `BB`, `DB` case (B). The oracle's queries are `[m, k, bits…]`. -/
theorem lemma_8_2 (u c r : ℚ) (hu : 0 < u) (huc : u < c) (hc : c < 1 / 2) (hr : 1 + u - c < r)
    (hr1 : r < 1) :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ (p q ℓ : ℚ) (ζ a₀ : ℝ), 0 < q → q < p → p ≤ 1 → 0 < ℓ → ℓ < u →
      0 < ζ → ζ < (c : ℝ) - u → (r : ℝ) < 1 - ζ → 0 < a₀ →
      ∃ (γ : ℝ) (N₁ e : ℕ) (BA DA BB DB : Program), 0 < γ ∧
        (∀ A : DistFamilyK,
          let cond : ℕ → Prop := fun N => ∃ k : ℕ, 2 ≤ k ∧ (k : ℝ) ≤ (N : ℝ) ^ (u : ℝ) ∧
            |expect (pdsMass N k p q)
                (highPart (q : ℝ) D₀ (signedMean fun G : Graph N => ((A N G k) true).toReal))|
              ≥ (N : ℝ) ^ (-(2 : ℝ))
          UnknownSizeB p q r c γ N₁ e BA (distOracleK A) cond ∧
            UnknownSizeD p q c γ N₁ e DA (distOracleK A) cond) ∧
        (∀ S : SearchFamilyK,
          let cond : ℕ → Prop := fun N => ∃ k : ℕ, (N : ℝ) ^ (ℓ : ℝ) ≤ k ∧ (k : ℝ) ≤ (N : ℝ) ^ (u : ℝ) ∧
            ∑ G : Graph N, ∑ C, pdsJoint N k p q G C * ((S N G k) C).toReal ≥ (N : ℝ) ^ (-a₀)
          UnknownSizeB p q r c γ N₁ e BB (searchOracleK S) cond ∧
            UnknownSizeD p q c γ N₁ e DB (searchOracleK S) cond) := by sorry

end PDSEquiv
