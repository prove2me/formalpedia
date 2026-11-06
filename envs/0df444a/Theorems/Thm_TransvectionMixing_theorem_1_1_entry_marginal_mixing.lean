-- Prove2me | Theorems.Thm_TransvectionMixing_theorem_1_1_entry_marginal_mixing
-- name    : TransvectionMixing.theorem_1_1_entry_marginal_mixing
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:22:07.741779+00:00
-- url     : https://prove2.me/theorems/9746ccbb-d84d-4f01-bca2-20ab72447126
-- title:
--   Theorem 1.1 — mixing of entry marginals of the transvection walk on $\mathrm{SL}_n(\mathbb F_q)$, with and without the skeleton
-- statement:
--   Let $n\ge 256$ and $q\ge Q_{\mathrm{all}}(n):=(5000n)^{6n^2}$. For every $0<\varepsilon\le 1/4$ and every nonempty $\mathcal S\subseteq[n]\times[n]$, the two guarantees
--   $$
--   d_{\mathcal S}(t)\le\varepsilon,\qquad \sup_X\Pr_{\sigma:|\sigma|=t}\bigl[d^\sigma_{\mathcal S}(X)>\varepsilon\bigr]\le\varepsilon \tag{3}
--   $$
--   hold at every integer time $t$ greater than the minimum applicable bound below:
--
--   | hypothesis | sufficient time |
--   |---|---|
--   | $\lvert\mathcal S\rvert\le n^2/10$ | $21\lvert\mathcal S\rvert+89n\log n+66n\log(1/\varepsilon)$ |
--   | arbitrary $\mathcal S$ | $37\lvert\mathcal S\rvert+135n\log n+100n\log(1/\varepsilon)$ |
--   | arbitrary $\mathcal S$ | $14n^2+80n\log n+80n\log(1/\varepsilon)$ |
--   | arbitrary $\mathcal S$ | $20n^2+24n\log(1/\varepsilon)$ |
--
--   These results are tight up to constant factors: there is an absolute constant $c>0$ such that, whenever either guarantee of (3) holds at time $t$,
--   $$
--   t\ \ge\ c\bigl(|\mathcal S|+n\log(n/\varepsilon)\bigr).
--   $$
--
--   Here the walk multiplies an initial $X\in\mathrm{SL}_n(\mathbb F_q)$ on the left by $t$ independent uniform transvections $I_n+aE_{J,I}$ (uniform distinct rows $I\ne J$, uniform $a\in\mathbb F_q$); $d_{\mathcal S}(t)$ is the worst-case total-variation distance of the observed entries from their stationary marginal $\pi_{\mathcal S}$, and $d^\sigma_{\mathcal S}(X)$ is the same distance conditional on the skeleton $\sigma$ (the row pairs) with only the coefficients random. Logarithms are natural.
--
--   The theorem says that any fixed set of entries of the transvection-walk matrix becomes statistically close to its stationary law after $\Theta(|\mathcal S|+n\log(n/\varepsilon))$ steps, even when the skeleton is revealed, which rules out every distinguisher reading only those entries.
--
--   **Formalization Note** The field is any `F : Type` with `[Field F] [Fintype F]` and $q$ is its cardinality.
--
--   Differences from the source:
--   - reading: "These results are tight up to constant factors" → ∃ absolute c > 0, chosen before n, F, ε, 𝒮, such that either guarantee of (3) at time t implies t ≥ c(|𝒮| + n log(n/ε)); reason: the abstract's Θ(|𝒮| + n log(n/ε)) and Corollary 6.4's absolute implied constants; the either-guarantee reading is the stronger one and holds (the conditional guarantee at ε gives d_𝒮 ≤ 2ε, and Props. 6.1–6.2 hold for every ε)
--   - encoding: t greater than the minimum applicable bound of table (4) → t exceeds at least one applicable row (row 1 only when |𝒮| ≤ n²/10); reason: same set of times
--   - encoding: every finite field with q ≥ Q_all(n) → every `F : Type` with `[Field F] [Fintype F]` and Q_all(n) ≤ card F; reason: every finite field has a copy in `Type`
--   - encoding: laws of the walk over uniform skeletons and uniform coefficients → normalized counts (`prob`, `skelLaw`, `entryLaw`, `piS`) over finite types; reason: Lean convention for finite uniform probability; same values
--   - encoding: rows [n] = {1, …, n}; update i ↦ j is left multiplication by Iₙ + aE_{ji} → rows Fin n (0-based); the update is `Matrix.transvection j i a`; reason: Lean indexing; same walk (direction checked in a proved sanity file)
--   - encoding: ‖·‖_TV → the published `MarkovMixing.tvDist` (max over events of |μ(A) − ν(A)|); reason: equals ½∑|μ − ν| on probability vectors; same values
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Theorem 1.1, eqs. (3)–(4), p.4

import Mathlib
import Definitions.Def_TransvectionMixing_dS
import Definitions.Def_TransvectionMixing_Tshears

namespace TransvectionMixing

/-- **Theorem 1.1** (mixing of entry marginals) (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §1.2.1, p.4). Let `n ≥ 256` and
`q ≥ Q_all(n) := (5000n)^{6n²}`. For every `0 < ε ≤ 1/4` and `∅ ≠ 𝒮 ⊆ [n] × [n]`,
`d_𝒮(t) ≤ ε` and `sup_X Pr_{σ:|σ|=t}[d^σ_𝒮(X) > ε] ≤ ε` (eq. (3)) at every integer time `t`
greater than the minimum applicable bound in table (4):
`21|𝒮| + 89n log n + 66n log(1/ε)` (if `|𝒮| ≤ n²/10`), `37|𝒮| + 135n log n + 100n log(1/ε)`,
`14n² + 80n log n + 80n log(1/ε)`, `20n² + 24n log(1/ε)`. These results are tight up to
constant factors.

**Formalization Note** "Greater than the minimum applicable bound" is the disjunction over the
applicable rows. "Tight up to constant factors" is read as: an absolute `c > 0`, chosen before
`n, q, ε, 𝒮`, such that either guarantee of (3) at time `t` forces
`t ≥ c(|𝒮| + n log(n/ε))`. Fields range over `Type`; `q = Fintype.card F`. -/
theorem theorem_1_1_entry_marginal_mixing :
    ∃ c : ℝ, 0 < c ∧
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ), 256 ≤ n →
        Qall n ≤ Fintype.card F →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∀ S : Finset (Fin n × Fin n), S.Nonempty →
          (∀ t : ℕ,
              (((S.card : ℝ) ≤ (n : ℝ) ^ 2 / 10 ∧
                  21 * (S.card : ℝ) + 89 * n * Real.log n + 66 * n * Real.log (1 / ε) < t) ∨
                37 * (S.card : ℝ) + 135 * n * Real.log n + 100 * n * Real.log (1 / ε) < t ∨
                14 * (n : ℝ) ^ 2 + 80 * n * Real.log n + 80 * n * Real.log (1 / ε) < t ∨
                20 * (n : ℝ) ^ 2 + 24 * n * Real.log (1 / ε) < t) →
              dS F S t ≤ ε ∧
                (⨆ X : Matrix.SpecialLinearGroup (Fin n) F, skelBadProb F S t X ε) ≤ ε) ∧
          ∀ t : ℕ,
            (dS F S t ≤ ε ∨
                (⨆ X : Matrix.SpecialLinearGroup (Fin n) F, skelBadProb F S t X ε) ≤ ε) →
              c * (S.card + n * Real.log (n / ε)) ≤ t := by sorry

end TransvectionMixing
