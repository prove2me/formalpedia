-- Prove2me | Theorems.Thm_SubmodMFG_Supplement_lemma_7_3
-- name    : SubmodMFG.Supplement.lemma_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:28:02.437823+00:00
-- url     : https://prove2.me/theorems/1c250da6-f7bc-42c7-a5a9-d8f835566a4d
-- title:
--   Lemma 7.3 — the projection $\tau\mapsto p\tau$ of a stopping time lands in $L$
-- statement:
--   In the optimal-stopping MFG of §7, under its standing assumptions and Assumption 7.2, for every stopping time $\tau\le T$ the conditional sub-distributions
--   $$(p\tau)_t(A)=P[\psi(X_t)\in A,\ t<\tau\mid\mathcal F^B_t],\qquad A\in\mathcal B(\mathbb R),\ t\in[0,T],$$
--   admit an $\mathcal M_{\le1}(\mathbb R)$-valued $\mathbb F^B$-progressively measurable version, and every such version belongs to $L$, i.e. $(p\tau)_t\le_{st}\mu^\psi_t$ $P$-a.s. for a.e. $t$, where $\mu^\psi_t=P[\psi(X_t)\in\cdot\mid\mathcal F^B_t]$.
--
--   The lemma makes the projection $p:E\to L$ of (7.2), and hence the best-response map $R=p\circ\hat R$, well defined.
--
--   **Formalization Note** "Well defined" is the existence of a progressively measurable version together with its membership in $L$.
--
--   Differences from the source:
--   - reading: p: E → L is well defined, pτ ∈ L → an F^B-progressive M≤1-valued version of (7.2) exists, and every such version lies in L; reason: (7.2) defines pτ only P-a.s. for each (t, A); the proof shows progressive measurability of a right-continuous version and (7.3)
--   - reading: the future-increment σ-field is printed with t ≤ s₁ ≤ s₁ ≤ T → t ≤ s₁ ≤ s₂ ≤ T; reason: the displayed generators are B_{s₂}−B_{s₁}, so the repeated s₁ is a typographical error
--   - reading: E[sup_t (f(t, X_t, µ^ψ_t) + g(t, X_t))] < ∞ (Assumption 7.2) → for some F^B-progressive version µ^ψ of P[ψ(X_t) ∈ · | F^B_t]; reason: µ^ψ is defined only up to versions; the paper writes a process
--   - encoding: stopping times τ ≤ T P-a.s.; conditional probabilities P[· | F^B_t] P-a.s.; J(τ, m) = E[…] → τ with values in [0, T] everywhere; identities for each (t, A) a.s. (Mathlib conditional expectation of indicators); J in [0, ∞] with f, g ≥ 0; reason: a null-set modification under the usual conditions; nonnegativity is Assumption 7.2 (2)
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §7.2, Lemma 7.3, p.30 ((7.2)–(7.3), p.29; Assumption 7.2, p.30)

import Mathlib
import Definitions.Def_SubmodMFG_Supplement_SubProb
import Definitions.Def_RepairSched_UsualConditions
import Definitions.Def_SubmodMFG_Supplement_Processes
import Definitions.Def_SubmodMFG_Supplement_StoppingMFG

open MeasureTheory

namespace SubmodMFG.Supplement

/-- **Lemma 7.3** — the projection `τ ↦ pτ` of (7.2) is well defined, `pτ ∈ L`.
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §7.2, Lemma 7.3, p.30: "The map p: E → L as in (7.2) is well defined; i.e.,
pτ ∈ L for any τ ∈ E." Here (7.2), p.29: "(pτ)_t(A) := P[ψ(X_t) ∈ A, t < τ | 𝓕^B_t], for all
A ∈ B(ℝ) and t ∈ [0, T]".

**Formalization Note.** Standing assumptions of §7.1 (`StopModel.Standing`) and Assumption 7.2.
"Well defined" is: the conditional sub-distributions (7.2) admit an `M≤1(ℝ)`-valued
`𝔽^B`-progressively measurable version, and every such version lies in `L` (it is `≤_L µ^ψ`). -/
theorem lemma_7_3 {Ω : Type*} [MeasurableSpace Ω] {d₁ d₂ : ℕ} (M : StopModel Ω d₁ d₂)
    (hM : M.Standing) (h72 : M.Assumption72) :
    ∀ τ : M.StopTime,
      (∃ m : ℝ → Ω → SubProb, m ∈ M.Lpr ∧ M.IsCondProj (fun t => {ω | t < τ.1 ω}) m) ∧
      ∀ m : ℝ → Ω → SubProb, m ∈ M.Lpr → M.IsCondProj (fun t => {ω | t < τ.1 ω}) m →
        m ∈ M.Lset := by sorry

end SubmodMFG.Supplement
