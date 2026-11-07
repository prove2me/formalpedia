-- Prove2me | Theorems.Thm_SamplingAC0_lemma_8
-- name    : SamplingAC0.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:45:47.304384+00:00
-- url     : https://prove2.me/theorems/55c71af7-7b33-489a-b012-b4f5ad85707f
-- title:
--   Lemma 8 — statistical distance to min-entropy
-- statement:
--   Let $P,S$ be distributions on a finite set $B$ with $\Delta(P,S)\le1-\epsilon$, where $0<\epsilon\le1/2$. Then there is a subset $S_0$ of the support of $S$ with $\mathbb P_P[S_0]\ge\epsilon/2$ such that, for every $x\in B$,
--
--   $$\mathbb P_P[x\mid S_0]\le\frac{4S(x)}{\epsilon^2}.$$
--
--   In particular the distribution $P$ conditioned on $S_0$ has min-entropy
--
--   $$H_\infty(P\mid S_0)\ge H_\infty(S)-c\log_2(1/\epsilon),$$
--
--   where $c>0$ is an absolute constant.
--
--   The lemma converts closeness in statistical distance into a min-entropy bound on a large piece of $P$, all of whose points lie in the support of $S$; it is the first step of the direct-product theorem.
--
--   **Formalization Note** The absolute constant $c$ is chosen before all objects.
--
--   Differences from the source:
--   - generalization: distributions over Σ^m → distributions on any finite type; reason: Σ^m is a finite type, so the statement specializes to the source
--   - encoding: c log(1/ϵ) in the c-notation (p.2) → one constant c > 0 chosen before all objects; logarithm base 2; reason: c-notation; the base is absorbed by c
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Lemma 8, p.5 (proof pp.5–6)

import Mathlib
import Definitions.Def_SamplingAC0_law
import Definitions.Def_SamplingAC0_tvDist
import Definitions.Def_SamplingAC0_minEntropy
set_option autoImplicit false

namespace SamplingAC0

/-- **Lemma 8 (statistical distance to min-entropy).** Riazanov–Viola, *Sampling Tools and the
Power of AC0*, STOC 2027 submission (manuscript sha256 99c33d30…), Lemma 8, p.5: "Let P, S be
distributions over Σ^m such that ∆(P, S) ≤ 1 − ϵ, where 0 < ϵ ≤ 1/2. Then there is a subset S_0 of
the support of S which has P_P[S_0] ≥ ϵ/2 and such that, for every x ∈ Σ^m,
P_P[x | S_0] ≤ 4S(x)/ϵ². In particular, the distribution P conditioned on P ∈ S_0 has min-entropy
≥ H_∞(S) − c log(1/ϵ)."

**Formalization Note.** Stated over any finite type `β` (Σ^m is one). The absolute constant `c`
of the last sentence comes first (c-notation, p.2); logarithms are base 2. -/
theorem lemma_8 : ∃ c : ℝ, 0 < c ∧ ∀ (β : Type) [Fintype β] (P S : PMF β) (ε : ℝ), 0 < ε →
    ε ≤ 1 / 2 → tvDist P S ≤ 1 - ε →
    ∃ S₀ : Set β, S₀ ⊆ S.support ∧ pr P S₀ ≥ ε / 2 ∧
      (∀ x, ((condOn P S₀) x).toReal ≤ 4 * (S x).toReal / ε ^ 2) ∧
      minEntropy (condOn P S₀) ≥ minEntropy S - c * Real.logb 2 (1 / ε) := by sorry

end SamplingAC0
