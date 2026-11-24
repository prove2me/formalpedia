-- Prove2me | Theorems.Thm_ReusableAssort_Hybrid_Supplement_theorem_EC_2
-- name    : ReusableAssort.Hybrid.Supplement.theorem_EC_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:21:49.16083+00:00
-- url     : https://prove2.me/theorems/a2a1f181-13f2-4fc7-93a3-9bd5ca255398
-- title:
--   Theorem EC.2 (corrected: running time polynomial also in the encoding length), ec7 — Algorithm 4 earns 1 − 1/√(c_min+3) of Expected-LP and runs in oracle-polynomial time
-- statement:
--   Consider the setting of §EC.7, in which rental times are infinite: a rented unit never returns. Let $c_{\min} = \min_i c_i$.
--
--   1. **Competitive ratio.** Let the instance satisfy the model assumptions and let $y^*$ be an optimal solution of Expected-LP$[\{F_t\}_{t=1}^T]$ with $\sum_{S\in\mathcal S} y^*_{S,t,z} = 1$ for all $t, z$. Then Algorithm 4 (simulation, discarding by the inventory-dependent thresholds $Q^I_{i,t}$ of the DP (EC.1), and sub-assortment sampling) earns
--   $$\mathbb E[\mathrm{Rev}_4] \ge \Bigl(1 - \frac{1}{\sqrt{c_{\min} + 3}}\Bigr)\,\mathrm{LP}(y^*).$$
--   2. **Running time.** Take rational data, write $m = \sum_t|\mathcal Z_t|$ for the number of types, and let $L$ bound the binary encoding length of every number of the instance (the choice probabilities on $\mathcal S$, the fees, the duration and type probabilities, and the inventories). There are a single program $P$ of the logarithmic-cost randomized oracle RAM and constants $C, k \in \mathbb N$ such that, for every such instance satisfying the model assumptions, every bound $L$ and every offline assortment oracle satisfying Assumption 3, with $B = C\,(n + T + m + L + 1)^k$:
--      - every run of $P$ in the world of the instance (with positive probability) halts within $B$ instructions, has total cost at most $B$, and has exactly one arrival followed by one inventory-feasible offer per period before the next arrival;
--      - there is an optimal solution $y^*$ of Expected-LP with $\sum_{S\in\mathcal S} y^*_{S,t,z} = 1$ such that, for every record $o$ of (type, offered assortment, choice) over the consumers,
--   $$\Pr\bigl[\text{the run of } P \text{ records } o\bigr] = \Pr\bigl[\text{Algorithm 4 with } y^* \text{ records } o\bigr].$$
--
--   So Algorithm 4 has an implementation of polynomial cost given the offline oracle, and by the first clause that implementation earns at least $(1 - 1/\sqrt{c_{\min}+3})$ times the LP value. This is a companion theorem; it is not used in the proof of the goal. For large inventories the ratio approaches $1$ faster than the $1 - \varepsilon^*(c_{\min})$ of the reusable case.
--
--   **Formalization Note** The running-time bound is uniform: $P$, $C$ and $k$ are chosen before the instance. The cost model charges the binary length of every number handled, so the program cannot handle unboundedly large numbers for free, and it cannot enumerate $\mathcal S$ or the inventory levels $0, \dots, c_i$ when these are exponential in the parameters. The machine and the world are the definitions OracleRAM and Alg4Oracle.
--
--   Differences from the source:
--   - reading: §EC.7: rental times are infinite (products never return) → hypothesis ∀ z i, g^z_i(T) = 1 in both clauses; the world of the running-time clause reveals choices but no returns; reason: in the base model durations lie in {1, …, T}; a unit with duration T rented at t ≥ 1 is out through T, so it never returns within the horizon
--   - encoding: DP (EC.1) for I ∈ [c_i] with 𝓔^I_{i,T+1} = 𝓔^0_{i,t} = 0 → E I y i m t defined for every m ≥ 0 with the same boundary values; Algorithm 4 reads it only at m = I_{i,t} ≤ c_i; reason: the extra values are never used
--   - reading: the model of §2.1 (types ⟨ϕ^z, r^z, G^z⟩, Assumptions 1–2, c_i ∈ ℤ₊, durations g^z_i on [T]) → the published base Instance.Assumptions: one finite type space, durations on {1, …, T}, ϕ^z(S, ·) a sub-probability on S, weak substitutability on 𝒮, 𝒮 nonempty and downward closed, r ≥ 0, c_i ≥ 1; reason: these are the base mission's disclosed readings of the model, reused unchanged by reference
--   - encoding: competitive ratio α against Expected-LP (Definition 1) → α · lpObj I y ≤ expected revenue, for every optimal y with Σ_S y_{S,t,z} = 1; reason: the paper's ratio without dividing by a possibly zero LP value, as in Theorems 1–3 of the base mission; p. 11 takes the optimal assignment normalized without loss of generality
--   - correction: 'runs in time Poly(n, T, Σ_{t∈[T]}|Z_t|)' → total log cost at most C·(n + T + m + L + 1)^k on every branch, with L a bound on the binary encoding length of every number of the instance (rational data); reason: a running-time bound for a computation that reads the numbers ϕ, r, g, F, c must depend on their encoding length: the proof (PDF 34–35) runs the ellipsoid method, citing Grötschel et al. (1981), whose bounds are polynomial in the encoding length of the data, and Lemma EC.1 writes Poly(τ, m) without it. In a bit model no bound in n, T, Σ|Z_t| alone is possible: exact arithmetic on fees and probabilities of unbounded length (already the comparison r^{z_t}_i ≥ Q of Algorithm 4) has unbounded cost. Irrational data are excluded from this rational numerical encoding
--   - reading: 'it runs in time … given oracle access to an offline algorithm for assortment optimization (Assumption 3)' → there is one program of the logarithmic-cost randomized oracle RAM, the same for all instances, whose runs halt within the bound on every branch with positive weight and whose record of (type, offered set, choice) has exactly the law of Algorithm 4 run with some optimal normalized LP solution y*; each halted history satisfies ValidOnlineTrace (one arrival and one inventory-feasible offer per period, in that order); reason: The paper requires an online inventory-feasible implementation. The logarithmic-cost rational RAM fixes the arithmetic and oracle-communication model; exact finite-range uniform sampling is an explicit primitive. Matching the observable law ties the program to Algorithm 4, while ValidOnlineTrace prevents extra arrivals, repeated offers or unavailable products. No worst-case fair-bit exact-sampling equivalence is asserted.
--   - reading: Σ_{t∈[T]} |Z_t| → m, with the type space Fin m; reason: the base model uses one finite type space, the disjoint union of the Z_t, so its size is Σ_t |Z_t|; a computation names types by their indices
--   - encoding: oracle access to the instance → data read through calls (parameters, c_i, membership in 𝒮, ϕ on 𝒮, r, g, F); assortments as bit masks; the oracle answers only nonnegative R̂ as Assumption 3 states; reason: ϕ has exponentially many values and 𝒮 may be exponentially large, so neither can be written out as input; a call pays for the lengths of its arguments and answer
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, p. ec7 (PDF 33), Theorem EC.2; restated p. ec16 (PDF 42), §EC.7, with its proof (Proposition 2 and the DP); Proposition 2 p. 10, its proof and Lemma EC.1 pp. ec8–ec9 (PDF 34–35); Assumption 3 p. 9

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Supplement_Alg4Oracle

namespace ReusableAssort.Hybrid.Supplement

theorem theorem_EC_2 :
    (∀ {n T : ℕ} [NeZero n] {Z : Type} [Fintype Z] [DecidableEq Z]
      (I : Instance n T Z), I.Assumptions → (∀ z i, I.g z i T = 1) →
      ∀ (y : ℕ → Z → Finset (Fin n) → ℝ), LPOptimal I y → Normalized I y →
        (1 - 1 / Real.sqrt ((cmin I : ℝ) + 3)) * lpObj I y ≤ expRevAlg4 I y) ∧
    (∃ (P : List Instr) (C k : ℕ),
      ∀ (n T m : ℕ) [NeZero n] (I : Instance n T (Fin m)) (D : RatData n T m) (L : ℕ)
        (orc : Fin m → (Fin n → ℚ) → Finset (Fin n)),
        I.Assumptions → (∀ z i, I.g z i T = 1) → D.Represents I → D.SizeLE I L →
        IsOfflineOracle I orc →
        (∀ b ∈ run (alg4World I D L orc) P (C * (n + T + m + L + 1) ^ k) Config.init,
            b.1 ≠ 0 → ∃ c, b.2 = some c ∧ c.cost ≤ C * (n + T + m + L + 1) ^ k ∧
              ValidOnlineTrace I c.hist) ∧
        ∃ y : ℕ → Fin m → Finset (Fin n) → ℝ, LPOptimal I y ∧ Normalized I y ∧
          ∀ o, runObsProb (run (alg4World I D L orc) P (C * (n + T + m + L + 1) ^ k)
            Config.init) o = alg4ObsProb I y o) := by sorry

end ReusableAssort.Hybrid.Supplement
