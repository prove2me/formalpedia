-- Prove2me | Theorems.Thm_SupplyRevenue_Supplement_theorem_1_2
-- name    : SupplyRevenue.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:34:13.762744+00:00
-- url     : https://prove2.me/theorems/4910397d-3cc3-4ed6-87f6-d28f893a6e29
-- title:
--   Theorem 1.2 — supplied-source recovery: $R/(32L_m)$ for subadditive buyers, $(1-\rho)R/128$ and $31(1-\rho)R/2048$ for $\mathcal H_2$, from samples and exact demand
-- statement:
--   Let $n,m\ge 1$, let $D$ be a finite rational instance (rational masses and values), let $\sigma$ be a rational source of revenue $R>0$, and let $\hat R\in\mathbb Q$ with $R\le\hat R\le 2R$. Put $K=\lceil\log_2(4m)\rceil$ and
--
--   $$L_m=1+\lceil\log_2(2048\,m^2)\rceil .$$
--
--   There are two pairs (training program, deployment program) of the sampled interface and one polynomial, all fixed before $n,m,D,\sigma,\hat R,\rho$, the residual order and the arrival order, with the following properties.
--
--   1. **Subadditive converter.** If every supported type is subadditive and $\sigma$ has aggregate caps at most $1$, then on input $(n,m,\hat R)$ the cost clauses hold and the inclusive revenue in every fixed order is at least $R/(32L_m)$.
--   2. **$\mathcal H_2$ algorithm.** If $D\in\mathcal H_2$ and $\rho\in\mathbb Q\cap(0,1)$, then on input $(n,m,\hat R,\rho)$, with no cap, partition or clause input:
--      - at aggregate caps at most $1$: the cost clauses hold with $\log(1/\rho)$; the inclusive revenue in every order is at least $(1-\rho)R/128$; with probability at least $1-\rho$ over training the deployed law earns at least $R/128$ in every order simultaneously; at $\rho=1/4$ the inclusive bound is $3R/512$;
--      - at caps $1/(2K)$: the same with $31(1-\rho)R/2048$, $31R/2048$ and $93R/8192$.
--   3. For every finite rational $\mathcal H_2$ instance and $0<\delta\le 1$, $A_\delta\le\frac{512}{3}\,\mathrm{OblivItemRev}$.
--   4. The worst cap and buy-many ratios of $\mathcal H_2$ have orders $1$ and $K$, and there is no constant $C$ with $B\le C\,A_1$ on all finite rational $\mathcal H_2$ instances.
--
--   The **cost clauses**: training halts with probability one, as does deployment from almost every stored output; type, source and demand-query counts are polynomial in $n$, $m$ and $\log(1/\rho)$ on every run; query, stored and deployed bit sizes are polynomial in these, the input sizes and the sizes of the observed source offers; and the expected numbers of fair coins are polynomial.
--
--   The theorem separates a general logarithmic-loss converter for subadditive buyers from constant recovery under the persistent but unknown partition promise $\mathcal H_2$; both convert a supplied source rather than discover one.
--
--   **Formalization Note** Revenues are in $[0,\infty]$, and inclusive revenue is $\mathbb E_{\text{training}}[\mathbb E_{\text{deploy}}[\mathrm{Rev}]]$. Caps at most $1$ and $1/(2K)$ are source feasibility at $\delta=1$ and $\delta=1/(2K)$. Here $\rho$ is the training failure probability, unrelated to the $\rho$ of §9, and $B$ is the buy-many benchmark.
--
--   Differences from the source:
--
--   - encoding: the constructions, with access to the sampled interface only → computable controllers mapping (rational input, transcript) to the next query among halt, fair coin, type draw with reusable handle, source draw, tie-ruled full-stock demand query; reason: a formal model of an oracle algorithm with exactly the access of p.3; the training input is (n, m, R̂) or (n, m, R̂, ρ), with no cap, partition or clause input
--   - encoding: one precommitted personalized matrix law; deployment uses fresh source/row coins → a second computable controller, run on [n, m] ++ stored data, with coins and source draws only, whose output list is decoded into a price matrix (prices clamped at 0); reason: stored data are rational response rules and weights; the law is fixed before arrivals and independent of types and order
--   - encoding: expected actual revenue including training failure; with probability at least 1 − ρ over training … in every independent fixed order simultaneously → inclusiveRev = E_training[E_deploy[Rev]] in ℝ≥0∞ with non-halting runs counted as 0; the high-probability clause is P_training[∀ π, E_deploy[Rev] ≥ bound] ≥ 1 − ρ; reason: literal semantics; ∀ π inside the event is the word 'simultaneously'
--   - reading: type, source and demand-query counts, and the bit lengths of rational prices and stored data, are polynomial in n, m, log(1/ρ) and the stated input/sample encodings → one polynomial c(1+x)^k fixed before n, m: on every run, counts ≤ poly(n + m + ⌈log₂(1/ρ)⌉); every query size, the stored data size and every deployed output size ≤ poly(n + m + ⌈log₂(1/ρ)⌉ + size R̂ + size ρ + total size of the source offers observed); reason: the counts are read against n, m, log(1/ρ) alone, the stronger of the two parses; the subadditive converter has no ρ (term 0)
--   - reading: the rejection-based sampling work is polynomial in expectation → training and deployment halt with probability one, and their expected numbers of fair coins are ≤ poly(n + m + ⌈log₂(1/ρ)⌉ + size R̂ + size ρ); reason: the program's own randomness is fair bits only, so the work of rejection sampling is its expected coin count
--   - encoding: the cost clauses for the H₂ algorithm (both cap rows) → stated under aggregate caps ≤ 1; reason: caps 1/(2K) ≤ 1 (K ≥ 2) imply caps ≤ 1, so the clause covers both H₂ rows
--   - encoding: normalized monotone subadditive buyers → every supported type satisfies the published SubmodOrder.Subadditive, v(S ∪ T) ≤ v(S) + v(T); reason: normalization and monotonicity are part of the base model; class membership concerns supported types (base reading R10)
--   - reading: every supported type satisfies v_i(T) = Σ_{j∈T} v_i({j}) on either block → additive on every subset of B₁ and on every subset of its complement; reason: 'either block' means each of the two blocks; one partition per buyer shared by its supported types
--   - reading: its worst cap and buy-many ratios have orders 1, K → ∃ C before m: A_δ ≤ C·Obl (0 < δ ≤ 1) and B ≤ C·K·Obl for every finite rational H₂ instance; ∃ c' > 0 before m: for every m ≥ 1 and 0 < δ ≤ 1 a rational H₂ instance on m items, chosen before the residual order, with 0 < Obl and c'·Obl ≤ A_δ, and one with 0 < Obl and c'·K·Obl ≤ B; reason: the base mission's reading R2 of Θ, against OblivItemRev as the sentence says
--   - reading: there is no constant B/A₁ comparison → ¬ ∃ C, B ≤ C·A₁ for every finite rational H₂ instance and residual order; reason: the negation of a uniform constant comparison
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), Theorem 1.2 (Supplied-source recovery), pp.3–4, with the Sampled interface paragraph, p.3

import Mathlib
import Definitions.Def_SupplyRevenue_Classes
import Definitions.Def_SupplyRevenue_CapRev
import Definitions.Def_SupplyRevenue_BuyMany
import Definitions.Def_SupplyRevenue_Revenue
import Definitions.Def_SupplyRevenue_Supplement_Classes
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_SupplyRevenue_Supplement_Sampled

open scoped ENNReal

namespace SupplyRevenue
namespace Supplement

open Classical in
/-- Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
Theorem 1.2 (Supplied-source recovery), pp.3–4, with the sampled interface of p.3.

There are computable sampled-interface programs — a training/deployment pair for subadditive buyers and one for `𝓗₂` —
and one polynomial `c(1+x)^k`, all fixed before `n, m`, the instance, the source, the residual order, `ρ`, the caps and
the order, such that for all `n, m ≥ 1`, finite rational instances `D`, rational sources `σ` with revenue
`R = sourceRev > 0` and calibrations `R ≤ R̂ ≤ 2R` (`R̂ ∈ ℚ`), with `L_m = 1 + ⌈log₂(2048 m²)⌉`, `K = ⌈log₂(4m)⌉`:
1. subadditive `D` (every supported type satisfies `v(S ∪ T) ≤ v(S) + v(T)`, the published `SubmodOrder.Subadditive`), caps `≤ 1`, input `(n, m, R̂)`: the cost clauses hold, and the inclusive revenue in every fixed order
   is at least `R/(32 L_m)`;
2. `D ∈ 𝓗₂`, `ρ ∈ ℚ ∩ (0, 1)`, input `(n, m, R̂, ρ)` (no cap, partition or clause input): the cost clauses hold with
   `log(1/ρ)`; at caps `≤ 1` the inclusive revenue is `≥ (1−ρ)R/128` in every order, with probability `≥ 1−ρ` over
   training the deployed law earns `≥ R/128` in every order simultaneously, and at `ρ = 1/4` the inclusive bound is
   `3R/512`; at caps `1/(2K)` the same with `31(1−ρ)R/2048`, `31R/2048` and `93R/8192`;
3. for finite rational `𝓗₂` instances, `A_δ ≤ (512/3)·OblivItemRev` for `0 < δ ≤ 1`;
4. the worst cap and buy-many ratios of `𝓗₂` have orders `1` and `K` (reading R2 against `OblivItemRev`): one `C`
   before `m` with `A_δ ≤ C·Obl` and `B ≤ C·K·Obl`, and one `c' > 0` before `m` with, for every `m ≥ 1` (and `δ`), a
   rational `𝓗₂` instance on `m` items, chosen before the residual order, with `0 < Obl` and `c'·Obl ≤ A_δ`, and one
   with `0 < Obl` and `c'·K·Obl ≤ B`;
5. there is no constant `C` with `B ≤ C·A₁` for all finite rational `𝓗₂` instances.

**Formalization Note** The cost clauses are `CostBounds`: termination with probability one, counts `≤ poly(n+m+⌈log₂(1/ρ)⌉)`
on every run, query, stored and deployed sizes `≤ poly(n+m+⌈log₂(1/ρ)⌉+size(R̂)+size(ρ)+observed source sizes)`, expected
fair coins `≤ poly(n+m+⌈log₂(1/ρ)⌉+size(R̂)+size(ρ))` (the subadditive converter has no `ρ`: `0` and no `size ρ`).
"Inclusive" is `E_training[E_deploy[Rev]]` with training failure included (`inclusiveRev`); "with probability at least
`1−ρ` … simultaneously" puts `∀ π` inside the training event. Caps `≤ 1` and `1/(2K)` are `FeasibleSource` at `δ = 1` and
`δ = 1/(2K)`. All revenues are in `ℝ≥0∞`. `ρ` is the training failure probability, not `ρ = n/k` of §9. -/
theorem theorem_1_2 :
    ∃ (trainS deployS trainH deployH : Controller) (c k : ℕ),
      Computable trainS ∧ Computable deployS ∧ Computable trainH ∧ Computable deployH ∧
      -- row 1: normalized monotone subadditive buyers, aggregate source caps at most one
      (∀ (n m : ℕ), 0 < n → 0 < m → ∀ (tie : Tie m) (D : Instance n m) (σ : Source n m) (Rhat : ℚ),
        IsRationalInstance D → InstanceInClass D (SubmodOrder.Subadditive (α := Fin m)) → IsRationalSource σ →
        FeasibleSource tie D 1 σ → 0 < sourceRev tie D σ → sourceRev tie D σ ≤ (Rhat : ℝ) →
        (Rhat : ℝ) ≤ 2 * sourceRev tie D σ →
        CostBounds trainS deployS c k tie D σ [(n : ℚ), (m : ℚ), Rhat] 0 (sizeQ Rhat) ∧
        ∀ π : Equiv.Perm (Fin n),
          ENNReal.ofReal (sourceRev tie D σ / (32 * ((1 + Nat.clog 2 (2048 * m ^ 2) : ℕ) : ℝ))) ≤
            inclusiveRev trainS deployS tie D σ [(n : ℚ), (m : ℚ), Rhat] π) ∧
      -- rows 2 and 3: 𝓗₂ buyers, one algorithm with input ρ and no cap input
      (∀ (n m : ℕ), 0 < n → 0 < m → ∀ (tie : Tie m) (D : Instance n m) (σ : Source n m) (Rhat ρ : ℚ),
        0 < ρ → ρ < 1 →
        IsRationalInstance D → InstanceInH2 D → IsRationalSource σ →
        0 < sourceRev tie D σ → sourceRev tie D σ ≤ (Rhat : ℝ) → (Rhat : ℝ) ≤ 2 * sourceRev tie D σ →
        (FeasibleSource tie D 1 σ →
          CostBounds trainH deployH c k tie D σ [(n : ℚ), (m : ℚ), Rhat, ρ] (logInv ρ)
            (sizeQ Rhat + sizeQ ρ)) ∧
        (FeasibleSource tie D 1 σ →
          (∀ π : Equiv.Perm (Fin n),
            ENNReal.ofReal ((1 - (ρ : ℝ)) * sourceRev tie D σ / 128) ≤
              inclusiveRev trainH deployH tie D σ [(n : ℚ), (m : ℚ), Rhat, ρ] π) ∧
          ENNReal.ofReal (1 - (ρ : ℝ)) ≤
            trainE trainH tie D σ [(n : ℚ), (m : ℚ), Rhat, ρ]
              (fun o => if ∀ π : Equiv.Perm (Fin n),
                  ENNReal.ofReal (sourceRev tie D σ / 128) ≤ deployRev deployH tie D σ o.out π
                then 1 else 0) ∧
          (ρ = 1 / 4 → ∀ π : Equiv.Perm (Fin n),
            ENNReal.ofReal (3 * sourceRev tie D σ / 512) ≤
              inclusiveRev trainH deployH tie D σ [(n : ℚ), (m : ℚ), Rhat, ρ] π)) ∧
        (FeasibleSource tie D (1 / (2 * (capK m : ℝ))) σ →
          (∀ π : Equiv.Perm (Fin n),
            ENNReal.ofReal (31 * (1 - (ρ : ℝ)) * sourceRev tie D σ / 2048) ≤
              inclusiveRev trainH deployH tie D σ [(n : ℚ), (m : ℚ), Rhat, ρ] π) ∧
          ENNReal.ofReal (1 - (ρ : ℝ)) ≤
            trainE trainH tie D σ [(n : ℚ), (m : ℚ), Rhat, ρ]
              (fun o => if ∀ π : Equiv.Perm (Fin n),
                  ENNReal.ofReal (31 * sourceRev tie D σ / 2048) ≤ deployRev deployH tie D σ o.out π
                then 1 else 0) ∧
          (ρ = 1 / 4 → ∀ π : Equiv.Perm (Fin n),
            ENNReal.ofReal (93 * sourceRev tie D σ / 8192) ≤
              inclusiveRev trainH deployH tie D σ [(n : ℚ), (m : ℚ), Rhat, ρ] π))) ∧
      -- A_δ ≤ (512/3) OblivItemRev for finite rational 𝓗₂ buyers
      (∀ (n m : ℕ), 0 < n → 0 < m → ∀ (tie : Tie m) (D : Instance n m),
        IsRationalInstance D → InstanceInH2 D → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          capRev tie D δ ≤ ENNReal.ofReal (512 / 3) * oblivRev tie D) ∧
      -- orders 1 and K: upper side
      (∃ C : ℝ, ∀ (n m : ℕ), 0 < n → 0 < m → ∀ (tie : Tie m) (D : Instance n m),
        IsRationalInstance D → InstanceInH2 D →
          (∀ δ : ℝ, 0 < δ → δ ≤ 1 → capRev tie D δ ≤ ENNReal.ofReal C * oblivRev tie D) ∧
          buyManyRev D ≤ ENNReal.ofReal (C * (capK m : ℝ)) * oblivRev tie D) ∧
      -- orders 1 and K: lower side
      (∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ, 0 < m →
        (∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ (n : ℕ) (_ : 0 < n) (D : Instance n m),
          IsRationalInstance D ∧ InstanceInH2 D ∧
            ∀ tie : Tie m, 0 < oblivRev tie D ∧ ENNReal.ofReal c' * oblivRev tie D ≤ capRev tie D δ) ∧
        ∃ (n : ℕ) (_ : 0 < n) (D : Instance n m),
          IsRationalInstance D ∧ InstanceInH2 D ∧
            ∀ tie : Tie m, 0 < oblivRev tie D ∧
              ENNReal.ofReal (c' * (capK m : ℝ)) * oblivRev tie D ≤ buyManyRev D) ∧
      -- no constant B/A₁ comparison
      ¬ ∃ C : ℝ, ∀ (n m : ℕ), 0 < n → 0 < m → ∀ (tie : Tie m) (D : Instance n m),
        IsRationalInstance D → InstanceInH2 D → buyManyRev D ≤ ENNReal.ofReal C * capRev tie D 1 := by sorry

end Supplement
end SupplyRevenue
