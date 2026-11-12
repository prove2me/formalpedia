-- Prove2me | Theorems.Thm_QuantumBA_PackedShares_lemma_4_5
-- name    : QuantumBA.PackedShares.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:44.807855+00:00
-- url     : https://prove2.me/theorems/9177a82b-7dc2-4720-bda8-16360e3834ff
-- title:
--   Lemma 4.5 — level induction: F_ℓ ≥ F_{ℓ−1} − β − τ − η on 𝓔
-- statement:
--   Consider QBA:PackedShares with symbolic parameters satisfying the standing assumptions, an execution, and an epoch entered before the first honest decision, with loss parameters $\beta,\tau,\eta\in(0,1)$ (§3.1). Suppose that, for the realized fault set at each level's common deadline, at most $\beta m_\ell$ level-$\ell$ budgets fail. Then on $\mathcal E$,
--   $$F_\ell\ge F_{\ell-1}-\beta-\tau-\eta\qquad\text{for every }\ell\in[h].$$
--
--   Overloaded nodes, sparse nodes and the remaining elections each lose a small fraction of the counted arrays.
--
--   Differences from the source:
--   - encoding: the parameters remain symbolic until Section 6 (b, w, h, committees, forwarding graphs, capacities) → the statement holds for every parameter record X : Ctx satisfying the standing assumptions WellFormed X of §1.1, §3.1, §5.1–§5.2; reason: the standing assumptions of the sections are written as one predicate; nothing beyond them is assumed
--   - encoding: events Bud_v, Fail_v, G_ℓ, F_ℓ, 𝓔 of an execution → functions of the execution prefix up to the relevant common deadline (Bud_v at d_v, outputs at e_v, Good at the end of distribution); reason: each event is determined by that prefix
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, p. 20, Lemma 4.5 (PDF p. 21)

import Mathlib
import Definitions.Def_QuantumBA_PackedShares_Analysis

namespace QuantumBA.PackedShares

open scoped BigOperators ENNReal Matrix

/-- Lemma 4.5 (level induction). -/
theorem lemma_4_5 {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] (X : Ctx n F)
    (hX : WellFormed X) (β τ η : ℝ) (hβ : 0 < β ∧ β < 1) (hτ : 0 < τ ∧ τ < 1)
    (hη : 0 < η ∧ η < 1) (x : Fin n → Bool) (A : Adv X) (e : ℕ)
    (ω : ℕ → Outcome F) (hω : IsExecution (qba X) x A X.t ω)
    (hentry : NoHonDec X x A (prefixH ω (epochStart X e)))
    (hfew : FewOverloaded X x A β (prefixH ω (delB X e X.h)) e)
    (hE : EventE X x A τ η (prefixH ω (delB X e X.h)) e) :
    ∀ ℓ, 1 ≤ ℓ → ℓ ≤ X.h →
      Fval X x A (prefixH ω (delB X e X.h)) e (ℓ - 1) - β - τ - η ≤ Fval X x A (prefixH ω (delB X e X.h)) e ℓ := by sorry

end QuantumBA.PackedShares
