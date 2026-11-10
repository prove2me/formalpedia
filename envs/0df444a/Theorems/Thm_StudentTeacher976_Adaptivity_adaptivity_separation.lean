-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_adaptivity_separation
-- name    : StudentTeacher976.Adaptivity.adaptivity_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:11:46.105721+00:00
-- url     : https://prove2.me/theorems/1539c1f3-02aa-4eaf-86f4-096f8370cb0d
-- title:
--   Theorem 1.4 — one extra round defeats polynomial parallelism
-- statement:
--   Let $i\ge0$ be any natural hierarchy level and assume
--
--   $$
--   \Sigma_{i+1}^p\not\subseteq\Delta_{i+1}^p/\mathrm{poly}.
--   $$
--
--   Let $r$ be any polynomial-time, nondecreasing, unbounded integer-valued function such that, for some real $\varepsilon>0$, $1\le r(m)\le m^{1-\varepsilon}$ for every positive input length $m$. Let $q$ be any polynomial-time integer-valued function with $1\le q(m)\le\mathrm{poly}(m)$, using one polynomial bound for all lengths. Then
--
--   $$
--   \mathrm{ST}^{\Sigma_i^p}[r(m)+1,1]\not\subseteq\mathrm{ST}^{\Sigma_i^p}[r(m),q(m)].
--   $$
--
--   Equivalently, some total polynomially bounded refutable search relation admits a uniform student with $r(m)+1$ sequential rounds and one candidate per round, but admits no uniform student with $r(m)$ rounds and $q(m)$ simultaneous candidates. The student at each round sees only earlier teacher batches; success is required for all histories and the teacher is unrestricted. Both classes concern the same underlying relation through a faithful presentation. The advice class in the hypothesis uses one fixed oracle machine and one polynomially bounded advice string shared by every input of a given length.
--
--   This is the entire adaptivity separation, with exact round counts, every hierarchy level, every permitted exponent, and every permitted $r,q$. In particular $q=1$ is included and no monotonicity or unboundedness is imposed on $q$.
--
--   Differences from the source:
--   - reading: increasing unbounded integer round functions → nondecreasing round functions, eventually above every constant; reason: strict increase on all naturals contradicts the sublinear regime; Appendix A uses nondecrease
--   - encoding: resource bounds on input lengths → bounds on positive lengths, resource values at length zero taken from length one; reason: avoids the undefined source convention at the empty input and preserves every positive-length count
--   - encoding: polynomial-time machines and polynomial hierarchy oracles → published finite OTM runs and alternating-quantifier hierarchy, fixed Sigma_i oracle and polynomial clocks; reason: standard polynomially equivalent operational models; their simulation and padding bridges remain proof obligations
--   - encoding: polynomial-time length functions and poly(m) bounds → unary numerical length input and output, with one Polynomial Nat upper bound; reason: lengths are raw problem sizes, and each permitted resource has one uniform polynomial bound
--   - encoding: TF search relations with bounded refutations and a uniform causal student → linked RefutablePresentation and ST predicates on all finite strings, exact refutation lengths, zero-based internal indices and self-delimiting machine interfaces; reason: padding preserves bounded certificates; interface encodings do not alter raw input lengths or round counts
--   - encoding: failure of the inclusion Sigma_(i+1) in Delta_(i+1)/poly → failure of set inclusion into a clocked oracle advice class with one advice string for all inputs of each length; reason: same language-class hypothesis, with advice uniformity and all polynomial bounds quantified before inputs
-- source:
--   Ondřej Ježil, Dimitrios Tsintsilidas, STOC 2027 submission #976 (October 2026), Theorem 1.4, p.7 (PDF p.7); Definitions 1.1–1.2, pp.6–7 (PDF pp.6–7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_Game

namespace StudentTeacher976.Adaptivity

/-- Theorem 1.4, p.7 (PDF p.7), Ježil–Tsintsilidas, STOC 2027 submission #976
(October 2026). All hierarchy levels and every source-admissible r and q are included.
The conclusion concerns the underlying total search relations, not a fixed run or teacher.
No good-pair, fixed-point, covering or normalization hypothesis enters this statement. -/
theorem adaptivity_separation (i : ℕ) (hardness : ¬ Sigma (i + 1) ⊆ DeltaPoly i)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q) :
    ¬ ST i (fun m => r m + 1) (fun _ => 1) ⊆ ST i r q := by sorry

end StudentTeacher976.Adaptivity
