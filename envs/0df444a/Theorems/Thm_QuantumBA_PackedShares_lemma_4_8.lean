-- Prove2me | Theorems.Thm_QuantumBA_PackedShares_lemma_4_8
-- name    : QuantumBA.PackedShares.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:14.29048+00:00
-- url     : https://prove2.me/theorems/74af467f-cd30-4f8d-b09b-7bfc5d6b4a15
-- title:
--   Lemma 4.8 — progress per epoch: failure probability at most p_n = δ + 2^{−w/2}
-- statement:
--   Consider QBA:PackedShares with symbolic parameters satisfying the standing assumptions and $\beta,\tau,\eta\in(0,1)$. Assume the sharing scheme provides fresh common coins and, for the fixed input vector and adversary, the hypotheses of Proposition 4.6 hold on every execution extending the epoch-entry history below. Conditional on any epoch-entry history before the first honest decision, the probability that the epoch ends with some correct process undecided is at most
--   $$p_n:=\delta+2^{-w/2}.$$
--
--   A uniform conditional bound on epoch failure gives a geometric tail for the number of epochs.
--
--   Differences from the source:
--   - encoding: the parameters remain symbolic until Section 6 (b, w, h, committees, forwarding graphs, capacities) → the statement holds for every parameter record X : Ctx satisfying the standing assumptions WellFormed X of §1.1, §3.1, §5.1–§5.2; reason: the standing assumptions of the sections are written as one predicate; nothing beyond them is assumed
--   - reading: the hypotheses of Proposition 4.6 hold → the fault-set hypothesis of Lemma 4.5 and F₀ − h(β+τ+η) > 1/2 hold, for the fixed input vector and adversary, on every execution extending the given epoch-entry history; reason: the hypotheses are events of the conditioned epoch; Corollary 4.9 supplies them on every execution via Lemma 4.4
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, p. 22, Lemma 4.8 (PDF p. 23)

import Mathlib
import Definitions.Def_QuantumBA_PackedShares_Analysis

namespace QuantumBA.PackedShares

open scoped BigOperators ENNReal Matrix

/-- Lemma 4.8 (progress per epoch). -/
theorem lemma_4_8 {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] (X : Ctx n F)
    (hX : WellFormed X) (β τ η : ℝ) (hβ : 0 < β ∧ β < 1) (hτ : 0 < τ ∧ τ < 1) (hη : 0 < η ∧ η < 1)
    (hfresh : FreshCoins X)
    (x : Fin n → Bool) (A : Adv X) (e : ℕ) (he : History F) (hlen : he.length = epochStart X e)
    (hpos : PosH X x A he) (hnd : NoHonDec X x A he)
    (hfew : ∀ ω, IsExecution (qba X) x A X.t ω → prefixH ω he.length = he →
      FewOverloaded X x A β (prefixH ω (delB X e X.h)) e)
    (hroot : ∀ ω, IsExecution (qba X) x A X.t ω → prefixH ω he.length = he →
      1 / 2 < Fval X x A (prefixH ω (delB X e X.h)) e 0 - X.h * (β + τ + η)) :
    condProb X x A he {ω | ∃ p, IsCorrect (qba X) x A X.t ω p ∧
        (qba X).decision ((cfgAt (qba X) x A X.t ω (startB n (gRound X (e + 1) 0))).st p) = none} ≤
      ENNReal.ofReal (pn X τ η) := by sorry

end QuantumBA.PackedShares
