-- Prove2me | Theorems.Thm_TransvectionMixing_corollary_6_4_entry_marginal_mixing_times
-- name    : TransvectionMixing.corollary_6_4_entry_marginal_mixing_times
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:21:47.346196+00:00
-- url     : https://prove2.me/theorems/577014f7-4359-4c00-8757-6576ff02cb1a
-- title:
--   Corollary 6.4 — entry-marginal mixing times are $\Theta(|\mathcal S|+n\log(n/\varepsilon))$
-- statement:
--   Let $n\ge 256$ and $0<\varepsilon\le 1/4$.
--
--   1. For every finite field $\mathbb F_q$ and every nonempty $\mathcal S\subseteq[n]\times[n]$, every integer $t\ge0$ with $d_{\mathcal S}(t)\le\varepsilon$ satisfies
--   $$
--   t\ \ge\ \max\Bigl\{\frac{|\mathcal S|-5/2}{1+2\log n/\log q},\ \frac{n-1}2\log\frac n{8\varepsilon}\Bigr\}.
--   $$
--   2. If $q\ge Q_{\mathrm{all}}(n)$, the least such time is $\Theta(|\mathcal S|+n\log(n/\varepsilon))$ with absolute implied constants: there are $c,C>0$, independent of $n,q,\varepsilon,\mathcal S$, such that some $t\le C(|\mathcal S|+n\log(n/\varepsilon))$ has $d_{\mathcal S}(t)\le\varepsilon$, and every such $t$ is at least $c(|\mathcal S|+n\log(n/\varepsilon))$.
--
--   It certifies that the upper bounds of the main theorem have the optimal order.
--
--   **Formalization Note** The least time is described by these two bounds rather than by an infimum, so no junk value arises when the set of times is empty. Fields range over `Type`.
--
--   Differences from the source:
--   - reading: the least such time is Θ(|𝒮| + n log(n/ε)), with absolute implied constants → ∃ c, C > 0 chosen before F, n, ε, 𝒮 such that some t ≤ C(|𝒮| + n log(n/ε)) has d_𝒮(t) ≤ ε and every t with d_𝒮(t) ≤ ε is ≥ c(|𝒮| + n log(n/ε)); reason: equivalent to the least time lying between the two bounds; avoids the junk value of an empty infimum
--   - encoding: every finite field 𝔽_q → every `F : Type` with `[Field F] [Fintype F]`, q = card F; reason: every finite field has a copy in `Type`
--   - encoding: laws of the walk over uniform skeletons and uniform coefficients → normalized counts (`prob`, `skelLaw`, `entryLaw`, `piS`) over finite types; reason: Lean convention for finite uniform probability; same values
--   - encoding: ‖·‖_TV → the published `MarkovMixing.tvDist` (max over events of |μ(A) − ν(A)|); reason: equals ½∑|μ − ν| on probability vectors; same values
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Corollary 6.4, p.35 (standing assumptions of §6.3, p.34)

import Mathlib
import Definitions.Def_TransvectionMixing_dS
import Definitions.Def_TransvectionMixing_Tshears

namespace TransvectionMixing

/-- **Corollary 6.4** (entry-marginal mixing times) (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §6.3, pp.34–35). Under §6.3's standing
assumptions `n ≥ 256` and `0 < ε ≤ 1/4`:

1. For every nonempty `𝒮 ⊆ [n] × [n]`, every integer `t ≥ 0` with `d_𝒮(t) ≤ ε` satisfies
   `t ≥ max{(|𝒮| − 5/2)/(1 + 2 log n/log q), ((n − 1)/2) log(n/(8ε))}`.
2. If `q ≥ Q_all(n)`, the least such time is `Θ(|𝒮| + n log(n/ε))` with absolute implied
   constants: there are `c, C > 0` (independent of `n, q, ε, 𝒮`) such that some
   `t ≤ C(|𝒮| + n log(n/ε))` has `d_𝒮(t) ≤ ε` and every such `t` is `≥ c(|𝒮| + n log(n/ε))`.

**Formalization Note** The least time is described by its two bounds instead of `sInf`, so no
junk value arises. Fields range over `Type`. -/
theorem corollary_6_4_entry_marginal_mixing_times :
    (∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ), 256 ≤ n →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∀ S : Finset (Fin n × Fin n), S.Nonempty →
        ∀ t : ℕ, dS F S t ≤ ε →
          max (((S.card : ℝ) - 5 / 2) / (1 + 2 * Real.log n / Real.log (Fintype.card F)))
            (((n : ℝ) - 1) / 2 * Real.log (n / (8 * ε))) ≤ t) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ), 256 ≤ n →
          Qall n ≤ Fintype.card F → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
          ∀ S : Finset (Fin n × Fin n), S.Nonempty →
            (∃ t : ℕ, dS F S t ≤ ε ∧ (t : ℝ) ≤ C * (S.card + n * Real.log (n / ε))) ∧
            ∀ t : ℕ, dS F S t ≤ ε → c * (S.card + n * Real.log (n / ε)) ≤ t := by sorry

end TransvectionMixing
