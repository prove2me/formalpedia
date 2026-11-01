-- Prove2me | Theorems.Thm_PartPredAlloc_lemma_EC_5
-- name    : PartPredAlloc.lemma_EC_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:18:11.579866+00:00
-- url     : https://prove2.me/theorems/59603263-efa2-4462-86aa-f87daa94bd6f
-- title:
--   Lemma EC.5, p.ec6 — concentration of the adversarial type-1 count $\zeta_1$ (corrected: $n_1\ge1$)
-- statement:
--   Let $n\ge3$, $p\in(0,1)$, let $\vec v_I$ contain $n_1\ge1$ type-1 customers, let $\lambda=t/n$ with $t\in\{1,\dots,n\}$ and $\epsilon\in(0,1/8]$. Then
--
--   $$
--   \Pr\Big(\big|\zeta_1-(1-p)\eta_1(\lambda)\big|\ge\sqrt{n_1\log\tfrac1\epsilon}\Big)\le\frac\epsilon4 .
--   $$
--
--   Here $\bar\epsilon_{EC.5}=1/8$ and $\alpha_{EC.5}=1$; $\zeta_1\sim\mathrm{Bin}(\eta_1(\lambda),1-p)$ counts the adversarial type-1 customers among the first $\lambda n$ positions.
--
--   Differences from the source:
--   - correction: for every instance → n₁ ≥ 1 (nType1 vI ≥ 1); reason: false at n₁ = 0: then ζ₁ = η₁(λ) = 0 and |0 − 0| ≥ √(0 · log(1/ε)) holds surely, probability 1 > ε/4; the only use (Lemma EC.1) supplies n₁ ≥ 1
--   - encoding: probability over the stochastic group S and the random permutation σ_S → prob n p: explicit finite sum with weights p^{|S|}(1−p)^{n−|S|} and σ uniform over the permutations fixing every position outside S; reason: the model has finitely many outcomes; this is its law (§3, p.10), with no measure theory
--   - encoding: λ ∈ {1/n, 2/n, …, 1} → t : ℕ with 1 ≤ t ≤ n and λ = t/n; reason: same set of times
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, Lemma EC.5, p.ec6 (PDF 43)

import Mathlib
import Definitions.Def_PartPredAlloc_EventEC1
import Definitions.Def_PartPredAlloc_obsCount

namespace PartPredAlloc

/-- **Lemma EC.5** (Hwang–Jaillet–Manshadi, arXiv:1810.00447v1, Lemma EC.5, p.ec6 = PDF 43),
corrected with `n₁ ≥ 1`. Let `ε̄_{EC.5} = 1/8` and `α_{EC.5} = 1`. For `ε ∈ (0, 1/8]` and
`λ = t/n ∈ {1/n, …, 1}`,
`P(|ζ₁ − (1 − p) η₁(λ)| ≥ √(n₁ log(1/ε))) ≤ ε/4`.

**Formalization Note.** The probability is over the outcome `(S, σ)`; `ζ₁` depends on `S` only.
Standing assumptions: `n ≥ 3`, `p ∈ (0, 1)`. Correction: with `n₁ = 0`, `ζ₁ = η₁ = 0` and the
event `|0 − 0| ≥ 0` is sure, so the printed statement is false; `n₁ ≥ 1` is added, which is what its
only use (Lemma EC.1) supplies. -/
theorem lemma_EC_5 {n : ℕ} (hn : 3 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (vI : Fin n → Cust) (hn1 : 1 ≤ nType1 vI) (t : ℕ) (ht1 : 1 ≤ t) (htn : t ≤ n)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 8) :
    prob n p (fun S _ => Real.sqrt ((nType1 vI : ℝ) * Real.log (1 / ε)) ≤
        |(ecZeta1 vI S t : ℝ) - (1 - p) * eta1 vI t|) ≤ ε / 4 := by sorry

end PartPredAlloc
