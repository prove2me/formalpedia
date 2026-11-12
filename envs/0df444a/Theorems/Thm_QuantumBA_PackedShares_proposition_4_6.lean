-- Prove2me | Theorems.Thm_QuantumBA_PackedShares_proposition_4_6
-- name    : QuantumBA.PackedShares.proposition_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:06.770099+00:00
-- url     : https://prove2.me/theorems/eadb9c54-0792-43c5-b9fe-9075bbb18fda
-- title:
--   Proposition 4.6 — root list: the root is successful and more than w/2 of its identifiers are counted
-- statement:
--   Consider QBA:PackedShares with symbolic parameters satisfying the standing assumptions, loss parameters $\beta,\tau,\eta\in(0,1)$ (§3.1), and an epoch entered before the first honest decision. Suppose the hypothesis of Lemma 4.5 holds and $F_0-h(\beta+\tau+\eta)>1/2$. Then on $\mathcal E$ the root is successful, its common list contains more than $w/2$ identifiers of $G_h$, and, if the sharing scheme provides fresh common coins, their final words are jointly uniform and independent of the selection history and the adversary's system.
--
--   The final words of these arrays provide the fresh common coins of final agreement.
--
--   **Formalization Note** For $h=0$ the root list is the public level-0 list. The last clause is stated at every selection history of positive probability on which the hypotheses and $\mathcal E$ hold.
--
--   Differences from the source:
--   - encoding: the parameters remain symbolic until Section 6 (b, w, h, committees, forwarding graphs, capacities) → the statement holds for every parameter record X : Ctx satisfying the standing assumptions WellFormed X of §1.1, §3.1, §5.1–§5.2; reason: the standing assumptions of the sections are written as one predicate; nothing beyond them is assumed
--   - encoding: events Bud_v, Fail_v, G_ℓ, F_ℓ, 𝓔 of an execution → functions of the execution prefix up to the relevant common deadline (Bud_v at d_v, outputs at e_v, Good at the end of distribution); reason: each event is determined by that prefix
--   - encoding: latent values S_ω with ρ_{S_{W′}E|h} = q^{-|W′|} Σ_s |s⟩⟨s| ⊗ ρ_{E|h} and reconstruction to S_ω → a family Λ h s of positive operators on the adversary’s registers, summing to the unnormalized adversary state at h and consistent in trace along histories, with the marginal identity on unopened words and Λ h s = 0 whenever a reconstruction by an honest requester returned a value ≠ s_ω; reason: this is the joint classical–quantum law of the latent values, the history and the adversary’s system
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, p. 20, Proposition 4.6 (PDF p. 21)

import Mathlib
import Definitions.Def_QuantumBA_PackedShares_Analysis

namespace QuantumBA.PackedShares

open scoped BigOperators ENNReal Matrix

/-- Proposition 4.6 (root list). -/
theorem proposition_4_6 {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] (X : Ctx n F)
    (hX : WellFormed X) (β τ η : ℝ) (hβ : 0 < β ∧ β < 1) (hτ : 0 < τ ∧ τ < 1)
    (hη : 0 < η ∧ η < 1) (x : Fin n → Bool) (A : Adv X) (e : ℕ) :
    (∀ ω, IsExecution (qba X) x A X.t ω →
      NoHonDec X x A (prefixH ω (epochStart X e)) →
      FewOverloaded X x A β (prefixH ω (delB X e X.h)) e →
      1 / 2 < Fval X x A (prefixH ω (delB X e X.h)) e 0 - X.h * (β + τ + η) →
      EventE X x A τ η (prefixH ω (delB X e X.h)) e →
      (1 ≤ X.h → Successful X x A (prefixH ω (delB X e X.h)) e X.h 0) ∧
      (X.w : ℝ) / 2 < (((if X.h = 0 then (List.range X.w).map (· + 1)
          else commonList X x A (prefixH ω (delB X e X.h)) e X.h 0).filter
          (fun y => y ∈ Gset X x A (prefixH ω (delB X e X.h)) e X.h)).length : ℝ)) ∧
    (FreshCoins X → ∀ hs : History F, hs.length = delB X e X.h → PosH X x A hs →
      NoHonDec X x A (hs.take (epochStart X e)) →
      FewOverloaded X x A β hs e →
      1 / 2 < Fval X x A hs e 0 - X.h * (β + τ + η) →
      EventE X x A τ η hs e →
      LatentValues X x A hs e ((Gset X x A hs e X.h).image (fun y => (y, Lbl.final)))
        (fun h' => h' = hs) (fun _ _ => False)) := by sorry

end QuantumBA.PackedShares
