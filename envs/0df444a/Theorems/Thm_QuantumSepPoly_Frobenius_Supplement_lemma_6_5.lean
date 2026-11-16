-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_Supplement_lemma_6_5
-- name    : QuantumSepPoly.Frobenius.Supplement.lemma_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:53:17.659509+00:00
-- url     : https://prove2.me/theorems/1cc6ab6d-c755-447f-adac-3b3ed0de41ee
-- title:
--   Lemma 6.5 — Runtime of the complete Section 6.2 reduction
-- statement:
--   Fix any constructor/sampler programs satisfying the full Lemma 6.4 contract, its uniform resource witnesses, and fixed source-admissible $\eta,t,\varepsilon$. There is a finite RAM program implementing the entire Section 6.2 output law, including the sampler timeout, matrix checks, exhaustive-search branch, fallback and tensor regrouping. Positive $C_\eta$ and natural $a_\eta$, chosen before every input and run, bound its charged arithmetic operations by
--   $$2^{C_\eta\sqrt{n+m+2}\,[\log_2(n+m+2)]^{a_\eta}}.$$
--   The bound holds on every 3-CNF and every random tape, including unsatisfiable inputs and failures. It includes serialization of every output matrix entry. The constructor contract is inherited support context and is not a hypothesis of Theorem 6.1.
--
--   Differences from the source:
--   - generalization: the fixed Lemma 6.4 construction → any finite-program construction satisfying its complete contract; reason: specialization to Lemma 6.4 recovers the source reduction
--   - encoding: polynomial or soft-exponential arithmetic time → positive coefficient and natural exponent witnesses with L=n+m+2, before every input and random run; reason: this unpacks the source asymptotic orders uniformly and includes finite input/output serialization
--   - encoding: the actual randomized reduction → a finite-program implementation with identical output law to the explicit reduction denotation; reason: independent draws may be scheduled differently while preserving the complete construction and law
--   - generalization: 3-CNF with three literal slots per clause → clauses with at most three occurrences, including empty clauses; reason: three-slot inputs embed directly; nonempty short clauses can be padded by repetition, and empty clauses have an immediate unsatisfiable branch without changing the resource order
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 6.5, p. 29 (PDF p. 29); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_Reduction

open scoped ENNReal

namespace QuantumSepPoly.Frobenius.Supplement
/-- Lemma 6.5, p.29: runtime for the complete §6.2 reduction.
The construction and sampler contract is supplied by Lemma 6.4; it is
not an assumption of the companion Theorem 6.1. -/
theorem lemma_6_5 (P Sample : RAMProgram) (q c : ℕ) (C C₀ : ℝ) (e a₀ : ℕ)
    (hq : 1 ≤ q) (hc : 1 ≤ c)
    (hconstruction : ConstructionSpec P Sample q (alphabetSize q) (degreeBound q c)
      (soundnessGap q c) C e C₀ a₀)
    (η : ℝ) (hη : 0 < η ∧ η < 1) (t : ℕ) (ε : ℚ)
    (hp : Admissible η (alphabetSize q) (degreeBound q c) (soundnessGap q c) t ε) :
    ∃ (R : RAMProgram) (hA : 0 < alphabetSize q) (Cη : ℝ) (aη : ℕ),
      0 < Cη ∧ ImplementsReduction R P Sample (alphabetSize q) hA η t ε C e ∧
      ∀ n m (f : CNF3 n m) r,
        MatrixTerminates R (cnfInput f) (softExpBound Cη aη n m) r := by sorry
end QuantumSepPoly.Frobenius.Supplement
