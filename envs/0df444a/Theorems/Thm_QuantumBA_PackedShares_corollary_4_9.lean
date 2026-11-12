-- Prove2me | Theorems.Thm_QuantumBA_PackedShares_corollary_4_9
-- name    : QuantumBA.PackedShares.corollary_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:02.398211+00:00
-- url     : https://prove2.me/theorems/16d85bbd-7c0c-4adc-b84e-39d970bffdd1
-- title:
--   Corollary 4.9 — from a sharing scheme to agreement, termination and expected cost
-- statement:
--   Consider QBA:PackedShares with symbolic parameters satisfying the standing assumptions, $\beta,\tau,\eta\in(0,1)$. Suppose the sharing scheme provides fresh common coins, the committees satisfy Lemma 4.4 at every level with corruption fraction $\gamma$, and $F_0-h(\beta+\tau+\eta)>1/2$ holds in every epoch entered before the first honest decision. Then agreement and validity hold on every execution. If moreover $p_n=\delta+2^{-w/2}<1$, termination holds with probability $1$, the expected number of epochs through the last correct halt is at most
--   $$(1-p_n)^{-1}+2,$$
--   and the expected cost is at most this number times any deterministic per-epoch cost bound.
--
--   Differences from the source:
--   - encoding: the parameters remain symbolic until Section 6 (b, w, h, committees, forwarding graphs, capacities) → the statement holds for every parameter record X : Ctx satisfying the standing assumptions WellFormed X of §1.1, §3.1, §5.1–§5.2; reason: the standing assumptions of the sections are written as one predicate; nothing beyond them is assumed
--   - encoding: expected number of epochs through the last correct halt; expected cost at most this number times a deterministic per-epoch cost bound → epochs = least E with R ≤ E·(rounds per epoch); a per-epoch bound is a bound on the qubits (bits) charged in every epoch of every execution; rounds per epoch are fixed; reason: direct transcription
--   - encoding: agreement and validity on every execution; termination with probability 1; expectations of Q, C, R → the law of an execution is the Ionescu–Tulcea measure of the Born-rule step kernels on infinite outcome sequences; an execution is an outcome sequence all of whose finite prefixes have positive probability; expectations are lower Lebesgue integrals of ℝ≥0∞-valued costs counted through the last halt of a correct process; reason: standard encoding of the probability space of the full-information model; no integrability side condition is needed
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, p. 22, Corollary 4.9 (PDF p. 23)

import Mathlib
import Definitions.Def_QuantumBA_PackedShares_Analysis

namespace QuantumBA.PackedShares

open scoped BigOperators ENNReal Matrix

/-- Corollary 4.9 (from a sharing scheme to agreement). -/
theorem corollary_4_9 {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] (X : Ctx n F)
    (hX : WellFormed X) (β τ η : ℝ) (hβ : 0 < β ∧ β < 1) (hτ : 0 < τ ∧ τ < 1) (hη : 0 < η ∧ η < 1)
    (hfresh : FreshCoins X)
    (hcomm : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ X.h →
      CommitteeProps X.ε β n X.t (X.m ℓ) (X.k ℓ) (fun i : Fin (X.m ℓ) => X.comm ℓ i))
    (hroot : ∀ (x : Fin n → Bool) (A : Adv X) (e : ℕ) ω, IsExecution (qba X) x A X.t ω →
      NoHonDec X x A (prefixH ω (epochStart X e)) →
      1 / 2 < Fval X x A (prefixH ω (delB X e X.h)) e 0 - X.h * (β + τ + η)) :
    (∀ (x : Fin n → Bool) (A : Adv X), Agreement (qba X) x A X.t ∧ Validity (qba X) x A X.t) ∧
    (pn X τ η < 1 → ∀ (x : Fin n → Bool) (A : Adv X),
      Termination (qba X) x A X.t ∧
      expect (qba X) x A X.t (fun ω => (epochsThroughHalt X x A ω : ℝ≥0∞)) ≤
        ENNReal.ofReal ((1 - pn X τ η)⁻¹ + 2) ∧
      (∀ BQ : ℝ, (∀ ω, IsExecution (qba X) x A X.t ω → ∀ e, (epochQ X x A ω e : ℝ) ≤ BQ) →
        expect (qba X) x A X.t (costQ (qba X) x A X.t) ≤ ENNReal.ofReal (((1 - pn X τ η)⁻¹ + 2) * BQ)) ∧
      (∀ BC : ℝ, (∀ ω, IsExecution (qba X) x A X.t ω → ∀ e, (epochC X x A ω e : ℝ) ≤ BC) →
        expect (qba X) x A X.t (costC (qba X) x A X.t) ≤ ENNReal.ofReal (((1 - pn X τ η)⁻¹ + 2) * BC)) ∧
      expect (qba X) x A X.t (fun ω => (roundsR (qba X) x A X.t ω : ℝ≥0∞)) ≤
        ENNReal.ofReal (((1 - pn X τ η)⁻¹ + 2) * X.epochLen)) := by sorry

end QuantumBA.PackedShares
