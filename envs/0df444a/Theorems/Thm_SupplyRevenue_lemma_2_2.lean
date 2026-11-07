-- Prove2me | Theorems.Thm_SupplyRevenue_lemma_2_2
-- name    : SupplyRevenue.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:46:54.512937+00:00
-- url     : https://prove2.me/theorems/96c1e930-076e-4e07-9186-e851e1c90ec8
-- title:
--   Lemma 2.2 — exact-cap separation
-- statement:
--   Let $\Omega$ be a set of pairs $(P,Z)$ of bounded nonnegative payments and nonnegative resource vectors, attainable by offers, and containing the empty pair $(0,0)$. Let $t\in\mathbb R$ and $b\ge 0$. Suppose that for every $c\ge 0$ and $\zeta>0$ a finite mixture from $\Omega$, using only pairs with $Z_j=0$ wherever $b_j=0$, satisfies
--
--   $$E[P-c\cdot Z]\ge t-c\cdot b-\zeta.$$
--
--   Then for every $\varepsilon>0$ a finite mixture from $\Omega$ has $EP\ge t-\varepsilon$ and $EZ\le b$ exactly.
--
--   It converts a cost-weighted response into exact caps, with no continuity of demand or attainment of a supremum.
--
--   Differences from the source:
--   - reading: payment statistics and resource vectors "attainable by type-independent offers" → an arbitrary set $\Omega$ of pairs $(P,Z)$ containing $(0,0)$, with finite mixtures of its elements as offer laws; reason: the lemma's proof uses only these properties; every use on the page is an instance
--   - reading: "If zero target coordinates can first be hidden while preserving this response" → the response mixture uses only pairs with $Z_j=0$ on $\{j:b_j=0\}$; reason: this pins the hiding step of the proof, "restrict to the zero-resource face"
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), Lemma 2.2, p.5

import Mathlib
import Definitions.Def_SupplyRevenue_Buyer

namespace SupplyRevenue

/-- Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
Lemma 2.2, p.5 (Exact-cap separation).

**Formalization Note** Stated abstractly: `Ω` is the set of primitive outcomes `(P, Z)` attainable by offers, containing
the empty outcome `(0, 0)`. `P` is bounded and nonnegative, `Z` nonnegative, the target `b ≥ 0`. An "offer law" is a
finite mixture of outcomes. "Zero target coordinates can first be hidden while preserving this response" is pinned as:
the response mixture for each `c, ζ` uses only outcomes with `Z_j = 0` on the face `{j : b_j = 0}`. The conclusion's caps
are exact, and its mixture again has atoms in `Ω`. -/
theorem lemma_2_2 {m : ℕ} (Ω : Set (ℝ × (Fin m → ℝ)))
    (hbdd : ∃ M, ∀ w ∈ Ω, w.1 ≤ M) (hP : ∀ w ∈ Ω, 0 ≤ w.1) (hZ : ∀ w ∈ Ω, ∀ j, 0 ≤ w.2 j)
    (hempty : ((0 : ℝ), (0 : Fin m → ℝ)) ∈ Ω) (t : ℝ) (b : Fin m → ℝ) (hb : ∀ j, 0 ≤ b j)
    (hresp : ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → ∀ ζ : ℝ, 0 < ζ →
      ∃ μ : Mix (ℝ × (Fin m → ℝ)), (∀ a, μ.atom a ∈ Ω) ∧
        (∀ a j, b j = 0 → (μ.atom a).2 j = 0) ∧
        t - ∑ j, c j * b j - ζ ≤ μ.E fun w => w.1 - ∑ j, c j * w.2 j) :
    ∀ ε : ℝ, 0 < ε → ∃ μ : Mix (ℝ × (Fin m → ℝ)), (∀ a, μ.atom a ∈ Ω) ∧
      t - ε ≤ μ.E (fun w => w.1) ∧ ∀ j, μ.E (fun w => w.2 j) ≤ b j := by sorry

end SupplyRevenue
