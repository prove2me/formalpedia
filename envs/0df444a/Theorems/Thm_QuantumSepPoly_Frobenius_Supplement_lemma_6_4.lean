-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_Supplement_lemma_6_4
-- name    : QuantumSepPoly.Frobenius.Supplement.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:52:05.006271+00:00
-- url     : https://prove2.me/theorems/ba451fad-8b87-458c-a6f8-aed3397b18a0
-- title:
--   Lemma 6.4 — Zero-knowledge sparse CSP construction
-- statement:
--   There are fixed finite constructor and sampler programs, an absolute query count $q\ge1$, expander degree $c\ge1$, and positive uniform polynomial/quasilinear witnesses. For every $n$-variable, $m$-clause 3-CNF, the constructor terminates in polynomial time on every run and outputs a nonempty sparse Boolean two-CSP with N=128(q+1)ℓ for an integer ℓ≥1 with constant alphabet $2^q$, degree bound $\delta=\max(q,c+1)$ and $N\le C_0L(\log_2L)^{a_0}$.
--
--   For every construction outcome of a satisfiable input, one probability law $D$ is fully satisfying and the returned sampler has exactly its marginal law on every $S$ with $|S|\le n+m+2$, in uniform expected polynomial time. If the input is unsatisfiable,
--   $$\Pr\{\operatorname{OPT}(I)\le1-\xi\}\ge99/100,\qquad\xi=1/[4cq(c+1)].$$
--   All programs and resource constants precede the formula; no correctness promise is supplied as an input.
--
--   Differences from the source:
--   - encoding: polynomial or soft-exponential arithmetic time → positive coefficient and natural exponent witnesses with L=n+m+2, before every input and random run; reason: this unpacks the source asymptotic orders uniformly and includes finite input/output serialization
--   - encoding: a returned randomized sampler → one finite sampler program with the constructor memory as its closure; reason: saved finite execution data supplies the outcome-specific sampler without oracle instructions
--   - encoding: constant-size alphabet and existential constants → Fin(2^q), δ=max(q,c+1), ξ=1/(4cq(c+1)); reason: these are exactly the choices in the source proof on p.26
--   - generalization: 3-CNF with three literal slots per clause → clauses with at most three occurrences, including empty clauses; reason: three-slot inputs embed directly; nonempty short clauses can be padded by repetition, and empty clauses have an immediate unsatisfiable branch without changing the resource order
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 6.4, p. 25 (PDF p. 25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_Construction
import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_Parameters

open scoped BigOperators ENNReal

namespace QuantumSepPoly.Frobenius.Supplement

theorem lemma_6_4 :
    ∃ (P Sample : RAMProgram) (q c : ℕ) (C : ℝ) (e : ℕ) (C₀ : ℝ) (a₀ : ℕ),
      1 ≤ q ∧ 1 ≤ c ∧
      ConstructionSpec P Sample q (alphabetSize q) (degreeBound q c) (soundnessGap q c) C e C₀ a₀ := by sorry

end QuantumSepPoly.Frobenius.Supplement
