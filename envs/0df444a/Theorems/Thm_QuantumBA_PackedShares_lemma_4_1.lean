-- Prove2me | Theorems.Thm_QuantumBA_PackedShares_lemma_4_1
-- name    : QuantumBA.PackedShares.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:00.449204+00:00
-- url     : https://prove2.me/theorems/bf16552e-a9bd-4359-ba98-2163fecc76e4
-- title:
--   Lemma 4.1 — one good phase of ByzantineAgreementWithCommonCoin
-- statement:
--   Consider one phase of ByzantineAgreementWithCommonCoin in QBA:PackedShares (a phase of an election, with threshold $a=a_C$, or a final phase, with $k=n$, $a=t$, where $n>3t$) and one component.
--
--   While at most $a$ members are corrupted: (i) no two honest members propose different bits for the component; (ii) no two honest members record different forced bits for it; (iii) if all honest estimates for the component equal $v$ at the start of the phase, every member honest at the end of the phase has estimate $v$.
--
--   Moreover, fix a history $h$ at the proposal deadline and suppose the coin bit of the phase is decoded identically by all members honest through decoding and is uniform conditioned on $h$. With $\mathrm{Comp}$ the event that at most $a$ members are corrupted through the end of the phase and $\mathrm{Split}$ the event that the honest estimates are not unanimous at the end of the phase,
--   $$\mathbb P[\mathrm{Comp}\wedge\mathrm{Split}\mid h]\le\tfrac12 .$$
--
--   Each fresh common coin aligns the honest estimates with probability at least one half.
--
--   **Formalization Note** Corruption counts are taken at the end of the round in question; the common coin is a measurable function of the execution.
--
--   Differences from the source:
--   - generalization: one phase of ByzantineAgreementWithCommonCoin (used by the elections and by final agreement) → every phase of every election and every final phase of QBA:PackedShares, for every parameter record with n > 3t; reason: the lemma concerns the procedure; it is stated for all its uses
--   - reading: honest members of the committee in the phase → members that are honest and not halted at the boundary considered; reason: a halted process takes no part in the phase; before the first honest decision nobody has halted
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, p. 16, Lemma 4.1 (PDF p. 17)

import Mathlib
import Definitions.Def_QuantumBA_PackedShares_Analysis

namespace QuantumBA.PackedShares

open scoped BigOperators ENNReal Matrix

/-- Lemma 4.1 (one good phase). -/
theorem lemma_4_1 {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] (X : Ctx n F)
    (hnt : 3 * X.t < n) (x : Fin n → Bool) (A : Adv X) (pr : PhaseRef) (c : ℕ)
    (hc : c < PhaseRef.width X pr) :
    -- (i) honest proposals do not conflict
    (∀ h : History F, h.length = bnd n (PhaseRef.r1 X pr) → PosH X x A h →
      ((PhaseRef.members X pr ∩ badAt X x A h h.length).card ≤ PhaseRef.thr X pr) →
      ∀ p q, Participates X x A h h.length pr p → Participates X x A h h.length pr q →
        ∀ b b', (propV X (viewAt X x A h h.length p) pr).getD c none = some b →
          (propV X (viewAt X x A h h.length q) pr).getD c none = some b' → b = b') ∧
    -- (ii) honest forced bits do not conflict
    (∀ h : History F, h.length = bnd n (PhaseRef.r1 X pr + 1) → PosH X x A h →
      ((PhaseRef.members X pr ∩ badAt X x A h h.length).card ≤ PhaseRef.thr X pr) →
      ∀ p q, Participates X x A h h.length pr p → Participates X x A h h.length pr q →
        ∀ b b', (forcedV X (viewAt X x A h h.length p) pr).getD c none = some b →
          (forcedV X (viewAt X x A h h.length q) pr).getD c none = some b' → b = b') ∧
    -- (iii) unanimity persists
    (∀ h : History F, h.length = bnd n (PhaseRef.r1 X pr + 3) → PosH X x A h →
      ((PhaseRef.members X pr ∩ badAt X x A h h.length).card ≤ PhaseRef.thr X pr) →
      ∀ v : Bool, (∀ p, Participates X x A h (startB n (PhaseRef.r1 X pr)) pr p →
          (estStart X (viewAt X x A h (startB n (PhaseRef.r1 X pr)) p) pr).getD c false = v) →
        ∀ p, Participates X x A h h.length pr p →
          (estEnd X (viewAt X x A h h.length p) pr).getD c false = v) ∧
    -- a fresh common coin aligns the estimates with probability at least 1/2
    (∀ h : History F, h.length = bnd n (PhaseRef.r1 X pr + 1) → PosH X x A h →
      ∀ cb : (ℕ → Outcome F) → Bool, Measurable cb →
      (∀ ω, IsExecution (qba X) x A X.t ω → prefixH ω h.length = h → ∀ p,
        Participates X x A (prefixH ω (bnd n (PhaseRef.r1 X pr + 3))) (bnd n (PhaseRef.r1 X pr + 3)) pr p →
        coinV X (viewAt X x A (prefixH ω (bnd n (PhaseRef.r1 X pr + 3))) (bnd n (PhaseRef.r1 X pr + 3)) p) pr = cb ω) →
      condProb X x A h {ω | cb ω = true} = 1 / 2 →
      condProb X x A h
        ({ω | (PhaseRef.members X pr ∩ badAt X x A (prefixH ω (bnd n (PhaseRef.r1 X pr + 3)))
              (bnd n (PhaseRef.r1 X pr + 3))).card ≤ PhaseRef.thr X pr} ∩
         {ω | ¬ ∃ v : Bool, ∀ p, Participates X x A (prefixH ω (bnd n (PhaseRef.r1 X pr + 3)))
              (bnd n (PhaseRef.r1 X pr + 3)) pr p →
            (estEnd X (viewAt X x A (prefixH ω (bnd n (PhaseRef.r1 X pr + 3)))
              (bnd n (PhaseRef.r1 X pr + 3)) p) pr).getD c false = v}) ≤ 1 / 2) := by sorry

end QuantumBA.PackedShares
