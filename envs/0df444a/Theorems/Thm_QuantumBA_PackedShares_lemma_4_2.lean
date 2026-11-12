-- Prove2me | Theorems.Thm_QuantumBA_PackedShares_lemma_4_2
-- name    : QuantumBA.PackedShares.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:52.491241+00:00
-- url     : https://prove2.me/theorems/345d6125-cb3b-4463-a139-53f80e7db5ab
-- title:
--   Lemma 4.2 — enough good phases: P[Comp ∧ Diff | h₀] ≤ u 2^{−g}
-- statement:
--   Consider one run of ByzantineAgreementWithCommonCoin in QBA:PackedShares (an election, $u$ components and $r$ phases, or a final agreement, one component and $w+1$ phases; $n>3t$). Fix a history $h_0$ no later than the start of the procedure. Suppose that for $g$ phases $j_1<\dots<j_g$, conditioned on any history at the proposal deadline of phase $j_i$, the coin bit of the phase is decoded identically by all members honest through decoding and is uniform. Let $\mathrm{Comp}$ be the event that at most $a$ members are corrupted through the output and $\mathrm{Diff}$ the event that two honest members output different vectors. Then
--   $$\mathbb P[\mathrm{Comp}\wedge\mathrm{Diff}\mid h_0]\le u\,2^{-g}. \tag{1}$$
--   While at most $a$ members are corrupted, every component unanimous among honest members at the start stays unchanged.
--
--   No independence between phases or components is needed.
--
--   Differences from the source:
--   - generalization: one phase of ByzantineAgreementWithCommonCoin (used by the elections and by final agreement) → every phase of every election and every final phase of QBA:PackedShares, for every parameter record with n > 3t; reason: the lemma concerns the procedure; it is stated for all its uses
--   - reading: honest members of the committee in the phase → members that are honest and not halted at the boundary considered; reason: a halted process takes no part in the phase; before the first honest decision nobody has halted
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, p. 17, Lemma 4.2 (PDF p. 18)

import Mathlib
import Definitions.Def_QuantumBA_PackedShares_Analysis

namespace QuantumBA.PackedShares

open scoped BigOperators ENNReal Matrix

/-- Lemma 4.2 (enough good phases). -/
theorem lemma_4_2 {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] (X : Ctx n F)
    (hnt : 3 * X.t < n) (x : Fin n → Bool) (A : Adv X) (P : ProcRef) :
    let ph := ProcRef.phase X P
    let K := ProcRef.numPhases X P
    let sB := startB n (PhaseRef.r1 X (ph 1))
    let oB := bnd n (PhaseRef.r1 X (ph K) + 3)
    let C := PhaseRef.members X (ph 1)
    let a := PhaseRef.thr X (ph 1)
    (∀ h₀ : History F, h₀.length ≤ sB → PosH X x A h₀ →
      ∀ (g : ℕ) (js : Fin g → ℕ), StrictMono js → (∀ i, 1 ≤ js i ∧ js i ≤ K) →
      (∀ i, ∀ h : History F, h₀ <+: h → h.length = bnd n (PhaseRef.r1 X (ph (js i)) + 1) → PosH X x A h →
        ∃ cb : (ℕ → Outcome F) → Bool, Measurable cb ∧
          (∀ ω, IsExecution (qba X) x A X.t ω → prefixH ω h.length = h → ∀ p,
            Participates X x A (prefixH ω (bnd n (PhaseRef.r1 X (ph (js i)) + 3)))
              (bnd n (PhaseRef.r1 X (ph (js i)) + 3)) (ph (js i)) p →
            coinV X (viewAt X x A (prefixH ω (bnd n (PhaseRef.r1 X (ph (js i)) + 3)))
              (bnd n (PhaseRef.r1 X (ph (js i)) + 3)) p) (ph (js i)) = cb ω) ∧
          condProb X x A h {ω | cb ω = true} = 1 / 2) →
      condProb X x A h₀
        ({ω | (C ∩ badAt X x A (prefixH ω oB) oB).card ≤ a} ∩
         {ω | ∃ p q, Participates X x A (prefixH ω oB) oB (ph K) p ∧
            Participates X x A (prefixH ω oB) oB (ph K) q ∧
            estEnd X (viewAt X x A (prefixH ω oB) oB p) (ph K) ≠
              estEnd X (viewAt X x A (prefixH ω oB) oB q) (ph K)}) ≤
        ENNReal.ofReal (PhaseRef.width X (ph 1) * (2 : ℝ) ^ (-(g : ℝ)))) ∧
    (∀ h : History F, h.length = oB → PosH X x A h → (C ∩ badAt X x A h oB).card ≤ a →
      ∀ c v, (∀ p, Participates X x A h sB (ph 1) p →
          (estStart X (viewAt X x A h sB p) (ph 1)).getD c false = v) →
        ∀ p, Participates X x A h oB (ph K) p →
          (estEnd X (viewAt X x A h oB p) (ph K)).getD c false = v) := by sorry

end QuantumBA.PackedShares
