-- Prove2me | Theorems.Thm_TalagrandThinning_corollary_1_3
-- name    : TalagrandThinning.corollary_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:43:12.264675+00:00
-- url     : https://prove2.me/theorems/a1c38c55-861c-4c6a-8498-39278c342991
-- title:
--   Corollary 1.3 — Talagrand's thinning conjecture: $J\cap X_\alpha\le_d X_p$ for $\alpha\le(\sqrt5-1)/2$
-- statement:
--   Fix $0<\alpha\le\frac{\sqrt5-1}{2}$. For every $N\ge1$, every $p\in(0,1)$ and every probability law $\nu$ on $\{0,1\}^N$ that is $\alpha p$-spread, let $J\sim\nu$ and let $X_\alpha\sim\mu_\alpha$ be independent of $J$. Then independent thinning gives
--
--   $$J\cap X_\alpha\le_d X_p,\qquad(1.5)$$
--
--   in both of the following senses:
--
--   1. the law of $J\cap X_\alpha$ is dominated by $\mu_p$: $T_\alpha\nu\le_d\mu_p$;
--   2. the original pair can be retained: there is a probability law on triples $(J,X_\alpha,X_p)$ under which $(J,X_\alpha)\sim\nu\otimes\mu_\alpha$, $X_p\sim\mu_p$, and $J\cap X_\alpha\subseteq X_p$ almost surely.
--
--   In particular $\alpha=1/2$ is a universal choice: both statements hold with $\alpha=1/2$ for every $N\ge1$, $p\in(0,1)$ and $(p/2)$-spread $\nu$.
--
--   This is Conjecture 7.8 of Talagrand (STOC 2010): a spread random set, thinned independently at a fixed rate, is stochastically dominated by a product random set of the matching density.
--
--   **Formalization Note** $\le_d$ is the paper's coupling definition (`StochDomSubset`), not the upset inequality (1.2). The second clause is the paper's own reading of "$X_p$ denotes a random set of law $\mu_p$ in a containing coupling", proved in the last paragraph of p.5.
--
--   Differences from the source:
--   - encoding: subsets $A\subseteq[N]=\{1,\dots,N\}$, $\cap$, $\subseteq$ → indicator vectors $x:\mathrm{Fin}\,N\to\mathrm{Bool}$ on $\{0,\dots,N-1\}$, $\sqcap$, $\le$; reason: the paper identifies a set with its indicator vector (p.2); relabelling the ground set changes no instance
--   - encoding: $\rho\le_d\sigma$: a coupling $(A,B)$ with $A\subseteq B$ a.s. → `StochDomSubset`: a probability measure on pairs with marginals $\rho,\sigma$ giving mass $0$ to $\{A\not\subseteq B\}$; reason: the paper's coupling definition (p.2) written as a measure on pairs
--   - encoding: a random set $J\sim\nu$, an independent mask $X_t\sim\mu_t$ and $T_t\nu=\mathcal L(J\cap X_t)$ → a probability measure `ν` on the cube, `prodLaw N t` (the weighted sum of point masses $\sum_x\mu_t(\{x\})\delta_x$) and `retention t ν`, the push-forward of the product measure `ν.prod (prodLaw N t)` under $(J,x)\mapsto J\sqcap x$; reason: laws of random sets on a finite cube, independence as the product measure; same instances
--   - reading: "$J\cap X_\alpha\le_d X_p$ … $X_p$ denotes a random set of law $\mu_p$ in a containing coupling" → both $T_\alpha\nu\le_d\mu_p$ and a triple coupling of $(J,X_\alpha,X_p)$ with $(J,X_\alpha)\sim\nu\otimes\mu_\alpha$, $X_p\sim\mu_p$, $J\cap X_\alpha\subseteq X_p$ a.s.; reason: the paper proves both readings (p.5); the conjunction is the stronger one and implies the other
--   - encoding: "In particular, $\alpha=1/2$ is a universal choice" → a second conjunct: the same statement at $\alpha=1/2$; reason: the sentence is an instance of the first conjunct, stated explicitly
-- source:
--   Fang & Wang, A Note on a Result of Chen Li: the Thinning Problem via the Kernel Method, arXiv:2609.18458 (held version dated Sep 12, 2026, sha256 68a0f38d…), Corollary 1.3, eq. (1.5), p.2; proof of Corollary 1.3 and the following paragraph, p.5

import Mathlib
import Definitions.Def_TalagrandThinning_IsSpread
import Definitions.Def_TalagrandThinning_retention
import Definitions.Def_TalagrandThinning_StochDomSubset

set_option autoImplicit false

open MeasureTheory

namespace TalagrandThinning

/-- Corollary 1.3 (Talagrand's thinning conjecture, [22, Conjecture 7.8])
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, Corollary 1.3, eq. (1.5), p.2; proof and the retained-pair paragraph, p.5).

Fix `0 < α ≤ (√5 − 1)/2`. For every `N ≥ 1`, every `p ∈ (0,1)` and every `αp`-spread probability
law `ν` of a random set `J`, with `X_α ∼ µ_α` independent of `J`:
(a) `J ∩ X_α ≤_d X_p`, i.e. `T_α ν ≤_d µ_p` (1.5);
(b) the original pair `(J, X_α)` can be retained: there is a probability law on triples
`(J, X_α, X_p)` whose `(J, X_α)`-marginal is `ν ⊗ µ_α`, whose `X_p`-marginal is `µ_p`, and under
which `J ∩ X_α ⊆ X_p` almost surely.
The second conjunct is the same statement for `α = 1/2` ("`α = 1/2` is a universal choice").

**Formalization Note** `≤_d` is `StochDomSubset` (the coupling definition of p.2), not the upset
inequality (1.2). Clause (b) is the paper's own reading of "`X_p` denotes a random set of law `µ_p`
in a containing coupling", proved in the last paragraph of p.5. -/
theorem corollary_1_3 :
    (∀ α : ℝ, 0 < α → α ≤ (Real.sqrt 5 - 1) / 2 →
      ∀ N : ℕ, 1 ≤ N → ∀ p : ℝ, 0 < p → p < 1 →
      ∀ ν : Measure (Cube N), IsProbabilityMeasure ν → IsSpread (α * p) ν →
        StochDomSubset (retention α ν) (prodLaw N p) ∧
        ∃ π : Measure (Cube N × Cube N × Cube N), IsProbabilityMeasure π ∧
          π.map (fun z : Cube N × Cube N × Cube N => (z.1, z.2.1)) = ν.prod (prodLaw N α) ∧
          π.map (fun z : Cube N × Cube N × Cube N => z.2.2) = prodLaw N p ∧
          π {z : Cube N × Cube N × Cube N | z.1 ⊓ z.2.1 ≤ z.2.2}ᶜ = 0) ∧
    (∀ N : ℕ, 1 ≤ N → ∀ p : ℝ, 0 < p → p < 1 →
      ∀ ν : Measure (Cube N), IsProbabilityMeasure ν → IsSpread ((1 / 2) * p) ν →
        StochDomSubset (retention (1 / 2) ν) (prodLaw N p) ∧
        ∃ π : Measure (Cube N × Cube N × Cube N), IsProbabilityMeasure π ∧
          π.map (fun z : Cube N × Cube N × Cube N => (z.1, z.2.1)) = ν.prod (prodLaw N (1 / 2)) ∧
          π.map (fun z : Cube N × Cube N × Cube N => z.2.2) = prodLaw N p ∧
          π {z : Cube N × Cube N × Cube N | z.1 ⊓ z.2.1 ≤ z.2.2}ᶜ = 0) := by sorry

end TalagrandThinning
