-- Prove2me | Theorems.Thm_SubnormalCover_muMeasure_ncard_biUnion
-- name    : SubnormalCover.muMeasure_ncard_biUnion
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-14T12:44:16.582904+00:00
-- url     : https://prove2.me/theorems/1ff332b8-4da1-4d2e-8ee4-8ef9e9ce1f95
-- title:
--   Totient measure of a union of an intersection-closed family
-- statement:
--   Let $\Gamma$ be a family of finite sets that is closed under intersection and satisfies $|S \cap T| = (|S|, |T|)$ (the greatest common divisor of the cardinalities) for all $S, T \in \Gamma$. Then for every finite subfamily $\Delta \subseteq \Gamma$ one has
--   $$\Bigl|\bigcup_{S \in \Delta} S\Bigr| \;=\; \mu\bigl(D(\{|S| : S \in \Delta\})\bigr),$$
--   where $D(R) = \{d \in \mathbb{Z}^{+} : d \mid m \text{ for some } m \in R\}$ is the divisor closure and $\mu(S) = \sum_{m \in S} \varphi(m)$ is the Berger–Felzenbaum–Fraenkel totient measure; the point is that the size of the union depends only on the *set* of cardinalities of the members, via Gauss's identity $\sum_{d \mid m} \varphi(d) = m$. This is the combinatorial engine behind Sun's Theorem 3.1 on unions of cosets, applied there to the family $\Gamma = \{X_d : d \mid N\}$ of arithmetic progressions $X_d = \{0 \le x < N : d \mid x\}$.
--
--   **Formalization note.** The members of $\Gamma$ are `Finset α` for a fixed ambient type `α` with decidable equality (no loss of generality: take `α` to be the union of the family), $\bigcup_{S \in \Delta} S$ is `Δ.biUnion id`, and $\{|S| : S \in \Delta\}$ is `Δ.image Finset.card`, which is genuinely a *set* of cardinalities — and in fact the hypothesis `hcard` already forces `Finset.card` to be injective on `Γ`, so nothing is collapsed. `divisorClosure` and `muMeasure` are the already-published `BFFPyramidal` arithmetic definitions, for which `divisorClosure {0} = ∅` and `muMeasure ∅ = 0`.
-- source:
--   Z.-W. Sun, On the Herzog-Schönheim conjecture for uniform covers of groups, J. Algebra 273 (2004) 153-175, https://doi.org/10.1016/S0021-8693(03)00526-X, Lemma 3.2, eq. (3.3)

import Mathlib
import Definitions.Def_BFFPyramidal_arithmetic

namespace SubnormalCover

open BFFPyramidal

theorem muMeasure_ncard_biUnion {α : Type*} [DecidableEq α] (Γ : Set (Finset α))
    (hinter : ∀ S ∈ Γ, ∀ T ∈ Γ, S ∩ T ∈ Γ)
    (hcard : ∀ S ∈ Γ, ∀ T ∈ Γ, (S ∩ T).card = Nat.gcd S.card T.card)
    (Δ : Finset (Finset α)) (hΔ : ↑Δ ⊆ Γ) :
    (Δ.biUnion id).card = muMeasure (divisorClosure (Δ.image Finset.card)) := by
  sorry

end SubnormalCover
