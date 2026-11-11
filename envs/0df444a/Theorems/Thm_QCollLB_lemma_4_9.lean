-- Prove2me | Theorems.Thm_QCollLB_lemma_4_9
-- name    : QCollLB.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:18:07.798946+00:00
-- url     : https://prove2.me/theorems/454c7a10-059f-4294-a8fe-6f784bf704e4
-- title:
--   Lemma 4.9 — first-row support of a multiplication operator
-- statement:
--   For every $i\in[m]$, $g:[m]\to\mathbb C$ and $\lambda\vdash m$,
--   $$
--   M_{i,g}P_\lambda\subseteq\bigoplus_{\substack{\mu\vdash m\\|\lambda_1-\mu_1|\le1}}P_\mu ,
--   $$
--   where $M_{i,g}|\pi\rangle=g(\pi(i))|\pi\rangle$ and $P_\lambda$ is the left-regular $\lambda$-isotypic subspace of $\mathbb C[S_m]$.
--
--   A single forward phase query therefore raises permutation degree by at most one.
--
--   Differences from the source:
--   - encoding: m → n; reason: renaming
--   - encoding: |λ_1 − μ_1| ≤ 1 → λ_1 ≤ μ_1 + 1 and μ_1 ≤ λ_1 + 1; reason: natural numbers, same condition
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Lemma 4.9, Eq. (27), p.22 (proof App. A.6, p.71)

import Mathlib
import Definitions.Def_QCollLB_Harmonic
import Definitions.Def_QCollLB_Queries

namespace QCollLB

open CompPermOracle OAI.PartialPermutation.DiagramCounting

/-- **Lemma 4.9 (First-row support of a multiplication operator)** (Peng–Wu, arXiv:2611.01767
(PDF sha256 4e5aba34…d9fc), Lemma 4.9, Eq. (27), p.22; proof App. A.6, p.71). For every `i ∈ [m]`,
`g : [m] → ℂ` and `λ ⊢ m`, `M_{i,g} P_λ ⊆ ⨁_{μ ⊢ m, |λ_1 − μ_1| ≤ 1} P_μ`.

**Formalization Note.** `m` is written `n`; `P_λ` is `CompPermOracle.block λ` (the left-regular
`λ`-isotypic subspace of `ℂ[S_n]`) and `λ_1` is `firstRow λ`; `|λ_1 − μ_1| ≤ 1` is written as the two
natural-number inequalities `λ_1 ≤ μ_1 + 1` and `μ_1 ≤ λ_1 + 1`. -/
theorem lemma_4_9 {n : ℕ} (i : Fin n) (g : Fin n → ℂ) (lam : Shape n) :
    (block lam).map (mulOp i g).toLinearMap ≤
      ⨆ (mu : Shape n) (_ : firstRow lam ≤ firstRow mu + 1 ∧ firstRow mu ≤ firstRow lam + 1),
        block mu := by sorry

end QCollLB
