-- Prove2me | Theorems.Thm_QGraphColl_lemma_2_4
-- name    : QGraphColl.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:10:41.484335+00:00
-- url     : https://prove2.me/theorems/26f19190-eea8-4bd1-a218-bd2058a0e136
-- title:
--   Lemma 2.4 — quantum counting, uniform marked samples and uniform-state preparation
-- statement:
--   Let $V$ be a vertex set with $n=|V|\ge2$, let $S\subseteq V$ be a known set of $a=|S|$ labels, and let $r=|S\cap M|$. There is an absolute constant $C'$ and, for every $c>0$, constants $C,K$ such that, with error $\epsilon=n^{-c}$ and $\tilde O(B)=C\,B\,(\log_2 n)^K$:
--
--   1. **Counting.** With $\tilde O(\sqrt a)$ queries an algorithm returns an integer $\hat r\in[0,a]$ which, on every input, except with probability $\epsilon$ is zero exactly when $r=0$ and otherwise satisfies
--   $$\frac r2\le\hat r\le2r,\qquad|\hat r-r|\le C'\sqrt r.$$
--   2. **Samples.** For every $s\ge0$ and $\hat r>0$ an algorithm with $\tilde O\big((s+1)\sqrt{a/\hat r}\big)$ queries either reports failure or returns $s$ labels; the returned labels are always marked labels of $S$. On a good estimate ($r\ne0$, $r/2\le\hat r\le2r$) it fails with probability at most $\epsilon$, and every $w\in(S\cap M)^s$ is returned with the same probability $\Pr[\text{success}]/r^s$, i.e. the batch consists of $s$ independent uniform marked samples.
--   3. **Preparation.** For every $\hat r>0$ an algorithm with $\tilde O(\sqrt{a/\hat r})$ queries ends, on every good estimate, within Euclidean distance $\epsilon$ of $\xi\otimes\frac{1}{\sqrt r}\sum_{v\in S\cap M}|v\rangle$, where $\xi$ is a fixed unit vector (not depending on $x$) on the remaining registers.
--
--   These are the counting and sampling primitives every routine of the algorithm uses.
--
--   **Formalization Note.** The label register of part 3 is the `V` component of the workspace `V × Fin m`. Outputs are measured outcomes mapped by `out`; part 1 requires $\hat r\le a$ for every outcome.
--
--   Differences from the source:
--   - encoding: Õ(B) and 'the assigned error probability' → ∃ C, K (chosen after the error exponent c, before the vertex type and all parameters) with T ≤ C·B·(log₂ n)^K, n = |V| ≥ 2, and error ≤ n^{−c} for every c > 0; reason: the paper's conventions: Õ suppresses factors polynomial in log n and logarithms are base two (p.12); error probabilities are inverse polynomial in n (p.14)
--   - reading: O(√r) in |r̂ − r| = O(√r) → C'·√r with C' > 0 fixed before the error exponent c; reason: the proof (p.46) counts to additive √r/10 + 1/100, an absolute constant
--   - reading: returns an integer r̂ ∈ [0, a] → out z ≤ a for every measurement outcome z; reason: the range is stated without the error qualifier; clamping makes it hold always
--   - reading: a batch of s independent uniform marked samples, reporting failure if insufficient samples are obtained → output none or some w : Fin s → V; with probability 1 every reported w i ∈ S ∩ M; on a good estimate P[w] · r^s = P[success] for every w ∈ (S ∩ M)^s; reason: the proof uses verified Grover trials, which return a marked label, uniform given success (p.46); exact uniformity is what 'independent uniform' says
--   - generalization: 'on a good estimate' (r/2 ≤ r̂ ≤ 2r and |r̂ − r| = O(√r)) → the ratio condition r ≠ 0, r ≤ 2r̂, r̂ ≤ 2r alone; reason: a weaker hypothesis makes parts 2 and 3 more general; every good estimate satisfies it
--   - reading: the uniform state over marked labels can be prepared to inverse polynomial precision → ‖final state − ξ ⊗ |S ∩ M⟩/√r‖ ≤ n^{−c} with ξ an input-independent unit vector and the label in a dedicated workspace register V; reason: 'prepared' means the remaining registers carry no input-dependent garbage; precision n^{−c} for every c is 'inverse polynomial'; the Euclidean distance also excludes an input-dependent global phase, the stronger of the two readings (a real-polynomial fixed-point amplification, [YLC14], achieves it)
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Lemma 2.4, p.13 (restated with proof, p.46)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QGraphColl_gc
import Definitions.Def_QGraphColl_eventProb

open QAlgorithms

namespace QGraphColl

/-- **Lemma 2.4** (Counting and marked samples; A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum
barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), p.13, restated p.46). Let a known set of
`a` labels contain `r` marked vertices. With `Õ(√a)` queries, quantum counting returns an integer
`r̂ ∈ [0, a]` that, except with the assigned error probability, is zero exactly when `r = 0` and
otherwise satisfies `r/2 ≤ r̂ ≤ 2r`, `|r̂ − r| = O(√r)`. Given `r̂ > 0`, a batch of `s` independent
uniform marked samples uses a fixed query limit `Õ((s+1)√(a/r̂))`, reporting failure if
insufficient samples are obtained. On a good estimate, sampling succeeds except with the assigned
error probability, and the uniform state over marked labels can be prepared to inverse polynomial
precision in `Õ(√(a/r̂))` queries.

**Formalization Note.**
* `Õ(B)` is `C · B · (log₂ n)^K` with `C, K` chosen after the error exponent `c` and before
  the vertex type and all parameters; "the assigned error probability" is `n^{-c}` for every `c > 0`
  (p.14: error probabilities are inverse polynomial in `n`), with `n = |V| ≥ 2`.
* The known set is `S ⊆ V`, `a = |S|`, `r = |S ∩ M|`. The constant `C'` of `O(√r)` is absolute
  (chosen first).
* Counting: an algorithm whose output `r̂` always lies in `[0, a]`, and which with probability
  `≥ 1 − n^{-c}` on every input satisfies the stated properties.
* Sampling: for each `s` and each `r̂ > 0`, an algorithm with output `none` (failure) or
  `some w`, `w : Fin s → V`. The reported samples are always marked labels of `S` (probability 1),
  and on a good estimate failure has probability `≤ n^{-c}` and every `w ∈ (S ∩ M)^s` has the same
  probability `P[success]/r^s`: the batch is exactly independent and uniform given success.
* Preparation: for each `r̂ > 0`, an algorithm with workspace `V × Fin m` (a label register `V`
  and an ancilla `Fin m`) and an input-independent unit vector `ξ` on the query register and
  ancilla, whose final state is within `n^{-c}` (Euclidean norm) of `ξ ⊗ |S ∩ M⟩/√r`, the uniform
  state over the marked labels of `S` in the label register.
* "A good estimate" in the second and third parts is the ratio condition `r ≠ 0`,
  `r/2 ≤ r̂ ≤ 2r` alone (it omits `|r̂ − r| = O(√r)`), which makes these parts more general. -/
theorem lemma_2_4 :
    ∃ C' : ℝ, 0 < C' ∧ ∀ c : ℝ, 0 < c → ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V], 2 ≤ Fintype.card V → ∀ S : Finset V,
        (∃ T : ℕ, (T : ℝ) ≤ C * Real.sqrt (S.card : ℝ) * Real.logb 2 (Fintype.card V : ℝ) ^ K ∧
          ∃ (m : ℕ) (A : QueryAlg V Bool (Fin m) T) (out : (V × Bool) × Fin m → ℕ),
            (∀ z, out z ≤ S.card) ∧
            ∀ x : V → Bool,
              eventProb A x out (fun rh =>
                (rh = 0 ↔ (S ∩ marked x).card = 0) ∧
                ((S ∩ marked x).card ≠ 0 →
                  (S ∩ marked x).card ≤ 2 * rh ∧ rh ≤ 2 * (S ∩ marked x).card ∧
                  |(rh : ℝ) - ((S ∩ marked x).card : ℝ)| ≤
                    C' * Real.sqrt ((S ∩ marked x).card : ℝ)))
                ≥ 1 - (Fintype.card V : ℝ) ^ (-c)) ∧
        (∀ s rh : ℕ, 0 < rh →
          ∃ T : ℕ, (T : ℝ) ≤ C * ((s : ℝ) + 1) * Real.sqrt ((S.card : ℝ) / rh) *
              Real.logb 2 (Fintype.card V : ℝ) ^ K ∧
            ∃ (m : ℕ) (A : QueryAlg V Bool (Fin m) T)
              (out : (V × Bool) × Fin m → Option (Fin s → V)),
              (∀ x : V → Bool,
                eventProb A x out (fun o => ∀ w, o = some w → ∀ i, w i ∈ S ∩ marked x) = 1) ∧
              ∀ x : V → Bool, (S ∩ marked x).card ≠ 0 → (S ∩ marked x).card ≤ 2 * rh →
                rh ≤ 2 * (S ∩ marked x).card →
                eventProb A x out (fun o => o = none) ≤ (Fintype.card V : ℝ) ^ (-c) ∧
                ∀ w : Fin s → V, (∀ i, w i ∈ S ∩ marked x) →
                  eventProb A x out (fun o => o = some w) * ((S ∩ marked x).card : ℝ) ^ s =
                    eventProb A x out (fun o => o ≠ none)) ∧
        (∀ rh : ℕ, 0 < rh →
          ∃ T : ℕ, (T : ℝ) ≤ C * Real.sqrt ((S.card : ℝ) / rh) *
              Real.logb 2 (Fintype.card V : ℝ) ^ K ∧
            ∃ (m : ℕ) (A : QueryAlg V Bool (V × Fin m) T)
              (ξ : EuclideanSpace ℂ ((V × Bool) × Fin m)),
              ‖ξ‖ = 1 ∧
              ∀ x : V → Bool, (S ∩ marked x).card ≠ 0 → (S ∩ marked x).card ≤ 2 * rh →
                rh ≤ 2 * (S ∩ marked x).card →
                ‖A.finalState (xorOracle x) -
                    WithLp.toLp 2 (fun q : (V × Bool) × (V × Fin m) =>
                      ξ (q.1, q.2.2) * (if q.2.1 ∈ S ∩ marked x then
                        ((Real.sqrt ((S ∩ marked x).card : ℝ) : ℂ))⁻¹ else 0))‖
                  ≤ (Fintype.card V : ℝ) ^ (-c)) := by sorry

end QGraphColl
