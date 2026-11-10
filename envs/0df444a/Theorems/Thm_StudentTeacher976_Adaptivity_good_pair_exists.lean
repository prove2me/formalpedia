-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_good_pair_exists
-- name    : StudentTeacher976.Adaptivity.good_pair_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:13:11.366206+00:00
-- url     : https://prove2.me/theorems/147941a2-808d-426e-8a1c-119d641d75f4
-- title:
--   Claim 3.1 — a good pair in every p(n)-element set
-- statement:
--   Fix a natural hierarchy level $i$ and a language $L$ presented by a bounded existential predicate in $\Delta_{i+1}^p$. Let $U$ be its positive $n$-bit instances. Let $r,q$ satisfy the admissible resource conditions, put $m=nk$, and suppose $k=r(m)\ge1$. Suppose a uniform tuple student, after the operational normalization from §3.1, solves the auxiliary relation supplying witnesses for all positive coordinates of each $k$-tuple, in $k$ rounds with $q(m)$ simultaneous candidates.
--
--   Use the fixed teacher that chooses the least uncovered positive coordinate and its lexicographically least valid witness, with fixed fillers elsewhere. It stops if every positive coordinate is covered in the batch. The pair $(S,x)$ is good when the actual run on the increasing enumeration of $S\cup\{x\}$ never returns the coordinate of $x$. Then
--
--   $$
--   \forall V\subseteq U,\quad |V|=k\ \Longrightarrow\ \exists x\in V:\ (V\setminus\{x\},x)\text{ is good}.
--   $$
--
--   This is the numbered supporting result for the source's good-pair construction. It assumes lower-round solvability, as the source preamble does, but no hardness hypothesis and no bound on the actual teacher trace. The statement includes $k=1$; if $|U|<k$, there is simply no eligible $V$.
--
--   Differences from the source:
--   - reading: increasing unbounded integer round functions → nondecreasing round functions, eventually above every constant; reason: strict increase on all naturals contradicts the sublinear regime; Appendix A uses nondecrease
--   - encoding: resource bounds on input lengths → bounds on positive lengths, resource values at length zero taken from length one; reason: avoids the undefined source convention at the empty input and preserves every positive-length count
--   - encoding: polynomial-time machines and polynomial hierarchy oracles → published finite OTM runs and alternating-quantifier hierarchy, fixed Sigma_i oracle and polynomial clocks; reason: standard polynomially equivalent operational models; their simulation and padding bridges remain proof obligations
--   - encoding: polynomial-time length functions and poly(m) bounds → unary numerical length input and output, with one Polynomial Nat upper bound; reason: lengths are raw problem sizes, and each permitted resource has one uniform polynomial bound
--   - generalization: the proof preamble takes q unbounded and increasing → q may be any source-admissible positive polynomially bounded function, including constant q; reason: Claim 3.1 is a fixed-length assertion with a fixed positive query count; no growth property of q is used and every source instance is retained
--   - encoding: L in Sigma_(i+1) with bounded existential Delta_(i+1) witness predicate → a WitnessPresentation of L with exact padded witness lengths; reason: the operational certificate presents exactly the source languages; a separate Sigma membership premise would be redundant
--   - encoding: a fixed size n with p(n)=r(m) and m=n p(n) → natural parameters n,k with k=resource r (n*k); reason: this is the same pointwise preamble with k denoting p(n), distinct from the refutation polynomial; positivity follows from the resource assumptions
--   - encoding: a normalized polynomial-time student on tuple inputs and full refutation tuples → one uniform structured tuple transducer with operational witness merging from earlier replies and current guesses; reason: makes witness retention and the source terminal batch-combination convention explicit without assuming correctness of a normalization theorem
--   - encoding: the fixed teacher never returns the index and witness for x in the ordered tuple → GoodPair uses the k-round terminal-aware fixedTrace and tests the input selected by each zero-based reply index; reason: least indices, lexicographically least witnesses and fillers are explicit; no trace-length or good-pair existence property is built in
--   - encoding: at most polynomially many candidate witness tuples in the proof preamble → exactly q(m) candidate tuples on legal histories, with exact padded witness lengths; reason: Definition 1.2 specifies q simultaneous queries; unused slots can be padded by repetition or dummy candidates, and bounded witnesses admit exact-length padding
-- source:
--   Ondřej Ježil, Dimitrios Tsintsilidas, STOC 2027 submission #976 (October 2026), Claim 3.1, p.20 (PDF p.20), with the §3.1 preamble on pp.19–20 (PDF pp.19–20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_Teacher

namespace StudentTeacher976.Adaptivity

/-- Claim 3.1, §3.1 p.20 (PDF p.20), Ježil–Tsintsilidas, STOC 2027 submission #976
(October 2026). The language is given by its bounded existential Δᵖᵢ₊₁ presentation.
The positive instance count k=p(n)=r(n*k) is distinct from the refutation polynomial
of Definition 1.1. The lower-round student is normalized operationally before play;
its universal-history success is the premise made in the source, not the conclusion.
No hardness assumption or bound on the fixed teacher's trace is assumed. -/
theorem good_pair_exists (i : ℕ) (L : Language) (W : WitnessPresentation i L)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q)
    (n k : ℕ) (hsize : k = resource r (n * k))
    (f : TupleStudent) (hf : UniformTupleStudent i f)
    (hshape : TupleStudentShape W n k (resource q (n * k)) f)
    (hsolve : TupleStudentWins W n k (resource q (n * k)) (normalize W f))
    (V : Finset Word) (hV : ∀ x ∈ V, x ∈ positiveInputs W n) (hcard : V.card = k) :
    ∃ x ∈ V, GoodPair W n k (resource q (n * k)) f (V.erase x) x := by sorry

end StudentTeacher976.Adaptivity
