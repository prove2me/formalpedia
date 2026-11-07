-- Prove2me | Theorems.Thm_QuasiStrictNE_lemma_1
-- name    : QuasiStrictNE.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:54.433197+00:00
-- url     : https://prove2.me/theorems/375619aa-3da9-40c1-8dc6-2f2793ccf4c7
-- title:
--   Lemma 1 — Euclidean projection onto $\Delta_k$: threshold, continuity, piecewise linearity, oracle algorithm
-- statement:
--   For $z\in\mathbb R^k$ ($k\ge 1$) let $z_{(1)}\ge\cdots\ge z_{(k)}$ be its coordinates in decreasing order and
--   $$
--   t_k(z)=\max_{1\le a\le k}\frac{\sum_{i=1}^a z_{(i)}-1}{a},\qquad \Pi_k(z)_i=\max\{z_i-t_k(z),0\}.
--   $$
--   Then:
--
--   1. $t_k(z)$ is the unique real number $t$ with $\sum_{i=1}^k\max\{z_i-t,0\}=1$;
--   2. $\Pi_k$ maps $\mathbb R^k$ into $\Delta_k$;
--   3. $\Pi_k$ is continuous;
--   4. $\Pi_k$ is piecewise linear: for finitely many hyperplanes, $\Pi_k$ is affine on every closed region cut out by choosing a side of each;
--   5. there is a polynomial-time algorithm with access to a linear-comparison oracle for $z\in\mathbb R^k$ that outputs the local affine formula $\Pi_k(z)=Cz+c$.
--
--   Differences from the source:
--   - encoding: z(1) ≥ ⋯ ≥ z(k), the coordinates in decreasing order → Multiset.sort (· ≥ ·) of the values of z; max over 1 ≤ a ≤ k as ⨆ over a : Fin k; reason: same numbers; k ≥ 1 makes the supremum a maximum
--   - reading: piecewise linear → a finite set of hyperplanes such that Π_k is affine (real C, c) on every closed sign region; reason: the paper's notion of pieces (p.16 regions R_T, closed)
--   - encoding: a polynomial-time algorithm interacting with a linear-comparison oracle → one step function, PolyTimeComputable on (instance, answers so far), run for q(|I|) rounds; queries coded by encRatVec/encRat, malformed queries answered false; output No = [false, false], or the tagged code of (C, c); reason: a model of the paper's oracle algorithms; every step and the whole run are polynomial in |I|
--   - encoding: algorithm with input z ∈ R^k (instance k) → instance k written in unary (k ones), domain all of ℝ^k (No is never output); reason: the algorithm outputs a k × k matrix, so polynomial time means polynomial in k
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Lemma 1, p.9

import Mathlib
import Definitions.Def_QuasiStrictNE_tk
import Definitions.Def_QuasiStrictNE_Proj
import Definitions.Def_QuasiStrictNE_OracleComputesLocalFormula

namespace QuasiStrictNE

open Matrix

/-- **Lemma 1 (Euclidean projection)** (Hansen & Nie, *On Existence and Computational Complexity of
Quasi-strict Equilibria*, arXiv:2611.06350, Lemma 1, p.9: "Then tk(z) is the unique real number t
satisfying ∑_{i=1}^k max{zi − t, 0} = 1. This projection maps R^k into ∆k, and is continuous and
piecewise linear. Moreover, there is a polynomial-time algorithm with access to a linear-comparison
oracle that outputs the local affine formula with input z ∈ R^k").

For every `k ≥ 1`:

1. for every `z ∈ ℝ^k`, `t = tk(z)` satisfies `∑ᵢ max(zᵢ − t, 0) = 1`, and it is the only real number
   that does;
2. the projection `Πk(z) = (max(zᵢ − tk(z), 0))ᵢ` lies in `Δk` for every `z ∈ ℝ^k`;
3. `Πk` is continuous;
4. `Πk` is piecewise linear: there are finitely many hyperplanes `a⊤z = b` such that on each closed
   region obtained by choosing a side of every hyperplane, `Πk(z) = Cz + c` for some matrix `C` and
   vector `c`;
5. one polynomial-time linear-comparison oracle algorithm, given `k` and oracle access to `z ∈ ℝ^k`,
   outputs a rational matrix `C` and vector `c` with `Πk(z) = Cz + c`.

**Formalization Note** `k ≥ 1` is the paper's standing convention (p.4, "For k ≥ 1, … ∆k"). In
clause 5 the instance `k` is written in unary (`k` ones), so "polynomial time" means polynomial in
`k`; the domain is all of `ℝ^k`, so the algorithm never outputs `No`. -/
theorem lemma_1 :
    (∀ k : ℕ, 1 ≤ k → ∀ z : Fin k → ℝ, ∑ i, max (z i - tk k z) 0 = 1 ∧
      ∀ t : ℝ, ∑ i, max (z i - t) 0 = 1 → t = tk k z) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ z : Fin k → ℝ, Proj k z ∈ stdSimplex ℝ (Fin k)) ∧
    (∀ k : ℕ, 1 ≤ k → Continuous (Proj k)) ∧
    (∀ k : ℕ, 1 ≤ k → ∃ H : Finset ((Fin k → ℝ) × ℝ), ∀ σ : (Fin k → ℝ) × ℝ → Bool,
      ∃ (C : Matrix (Fin k) (Fin k) ℝ) (c : Fin k → ℝ), ∀ z : Fin k → ℝ,
        (∀ h ∈ H, if σ h then h.1 ⬝ᵥ z ≤ h.2 else h.2 ≤ h.1 ⬝ᵥ z) → Proj k z = C *ᵥ z + c) ∧
    OracleComputesLocalFormula (ι := {k : ℕ // 1 ≤ k}) (fun k => List.replicate k.1 true)
      (fun k => k.1) (fun k => k.1) (fun _ => Set.univ) (fun k => Proj k.1) := by sorry

end QuasiStrictNE
