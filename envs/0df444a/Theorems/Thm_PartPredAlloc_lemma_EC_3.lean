-- Prove2me | Theorems.Thm_PartPredAlloc_lemma_EC_3
-- name    : PartPredAlloc.lemma_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:18:18.203529+00:00
-- url     : https://prove2.me/theorems/d5a70418-662a-473b-b4b0-4deab4baeaa6
-- title:
--   Lemma EC.3, p.ec5 — on (EC.1a)–(EC.1c), $ZR_1/R$ is within $4\sqrt{n_1\log(1/\epsilon)}$ of $\lambda pn_1$
-- statement:
--   Let $n\ge3$, $p\in(0,1)$, $\lambda=t/n$ with $t\in\{1,\dots,n\}$ and $\epsilon\in(0,1/24]$, and suppose $n_1>\frac{4}{p^2}\log\frac1\epsilon$. For every stochastic group $\mathcal S$ on which (EC.1a)–(EC.1c) hold,
--
--   $$
--   \frac{ZR_1}{R}\in\Big(\lambda pn_1-4\sqrt{n_1\log\tfrac1\epsilon},\ \lambda pn_1+4\sqrt{n_1\log\tfrac1\epsilon}\Big).
--   $$
--
--   Here $\alpha_{EC.3}=4$ and $k_{EC.3}=4$. Since $ZR_1/R$ is the conditional mean of $Z_1$, together with Lemma EC.2 this gives (EC.4): the conditional mean of $Z_1$ is close to $pn_1\lambda$.
--
--   Differences from the source:
--   - encoding: conditioned on the events (EC.1a)–(EC.1c) → for every S satisfying EventEC1 (a deterministic statement); reason: the conclusion is a function of (R, R₁, Z), so conditioning on the event means it holds on every outcome of the event
--   - reading: ε unrestricted in the lemma → ε ∈ (0, 1/24]; reason: the lemma is stated with Lemma EC.2's ε, and the paper uses it only "for ε ∈ (0, ε̄_{EC.2}]" (p.ec5)
--   - encoding: λ ∈ {1/n, 2/n, …, 1} → t : ℕ with 1 ≤ t ≤ n and λ = t/n; reason: same set of times
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, Lemma EC.3, p.ec5 (PDF 42)

import Mathlib
import Definitions.Def_PartPredAlloc_EventEC1

namespace PartPredAlloc

/-- **Lemma EC.3** (Hwang–Jaillet–Manshadi, arXiv:1810.00447v1, Lemma EC.3, p.ec5 = PDF 42). Let
`α_{EC.3} = 4` and `k_{EC.3} = 4`. Conditioned on the events (EC.1a)–(EC.1c), and when
`n₁ > (4/p²) log(1/ε)`, we have
`Z R₁ / R ∈ (λpn₁ − 4√(n₁ log(1/ε)), λpn₁ + 4√(n₁ log(1/ε)))`.

**Formalization Note.** The statement is deterministic: it holds for every stochastic group `S`
satisfying (EC.1a)–(EC.1c) (`EventEC1`) at `λ = t/n`, `t ∈ {1, …, n}`. The range `ε ∈ (0, 1/24]`
is the one in which the paper uses it (p.ec5: "for ε ∈ (0, ε̄_{EC.2}]"). `R > 0` follows from the
hypotheses. Standing assumptions: `n ≥ 3`, `p ∈ (0, 1)`. -/
theorem lemma_EC_3 {n : ℕ} (hn : 3 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (vI : Fin n → Cust) (t : ℕ) (ht1 : 1 ≤ t) (htn : t ≤ n)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 24)
    (hn1 : (nType1 vI : ℝ) > 4 / p ^ 2 * Real.log (1 / ε))
    (S : Finset (Fin n)) (hS : EventEC1 p ε vI S t) :
    (t : ℝ) / n * p * nType1 vI - 4 * Real.sqrt ((nType1 vI : ℝ) * Real.log (1 / ε)) <
        (ecZ S t : ℝ) * ecR1 vI S / ecR S ∧
      (ecZ S t : ℝ) * ecR1 vI S / ecR S <
        (t : ℝ) / n * p * nType1 vI + 4 * Real.sqrt ((nType1 vI : ℝ) * Real.log (1 / ε)) := by sorry

end PartPredAlloc
