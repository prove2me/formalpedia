-- Prove2me | Theorems.Thm_QuantumBA_PackedShares_lemma_4_7
-- name    : QuantumBA.PackedShares.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:40.713531+00:00
-- url     : https://prove2.me/theorems/2374d1e0-1a60-41b9-a828-93cbb194c369
-- title:
--   Lemma 4.7 — safety for any coins
-- statement:
--   For QBA:PackedShares with any parameters and any coins, if $n>3t$: agreement and validity hold on every execution, and after the first honest decision every correct process decides the same value by the end of the next final phase.
--
--   Safety depends only on the thresholds of final agreement and on delayed halting, not on the quality of the coins.
--
--   Differences from the source:
--   - encoding: after the first honest decision, every correct process decides the same value by the end of the next final phase → if the first honest decision is v (by p at the proposal deadline of final phase g, no honest decision earlier), every correct process has decided v at the end of final phase g+1; reason: decisions occur only at final proposal deadlines
--   - encoding: agreement and validity on every execution; termination with probability 1; expectations of Q, C, R → the law of an execution is the Ionescu–Tulcea measure of the Born-rule step kernels on infinite outcome sequences; an execution is an outcome sequence all of whose finite prefixes have positive probability; expectations are lower Lebesgue integrals of ℝ≥0∞-valued costs counted through the last halt of a correct process; reason: standard encoding of the probability space of the full-information model; no integrability side condition is needed
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, p. 22, Lemma 4.7 (PDF p. 23)

import Mathlib
import Definitions.Def_QuantumBA_PackedShares_Analysis

namespace QuantumBA.PackedShares

open scoped BigOperators ENNReal Matrix

/-- Lemma 4.7 (safety for any coins). -/
theorem lemma_4_7 {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] (X : Ctx n F)
    (hnt : 3 * X.t < n) (x : Fin n → Bool) (A : Adv X) :
    Agreement (qba X) x A X.t ∧ Validity (qba X) x A X.t ∧
    ∀ ω, IsExecution (qba X) x A X.t ω → ∀ (g : ℕ) (p : Fin n) (v : Bool),
      -- the first honest decision is `v`, by `p`, at the proposal deadline of final phase `g`
      p ∉ badAt X x A (prefixH ω (bnd n (finalPhaseRound X g + 1))) (bnd n (finalPhaseRound X g + 1)) →
      (qba X).decision (viewAt X x A (prefixH ω (bnd n (finalPhaseRound X g + 1)))
        (bnd n (finalPhaseRound X g + 1)) p) = some v →
      NoHonDec X x A (prefixH ω (bnd n (finalPhaseRound X g + 1) - 1)) →
      ∀ q, IsCorrect (qba X) x A X.t ω q →
        (qba X).decision (viewAt X x A (prefixH ω (bnd n (finalPhaseRound X (g + 1) + 3)))
          (bnd n (finalPhaseRound X (g + 1) + 3)) q) = some v := by sorry

end QuantumBA.PackedShares
