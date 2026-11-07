-- Prove2me | Theorems.Thm_QCopyMono_lemma_5
-- name    : QCopyMono.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:43:32.036208+00:00
-- url     : https://prove2.me/theorems/21da1577-7b50-4a1b-897c-161ad1179f6b
-- title:
--   Lemma 5 — a bipartite violation subgraph at a scale $d$ with $|B|/2^n\ge c\varepsilon d^{-5/8}$
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $n\ge1$ and let $f:\{0,1\}^n\to\{0,1\}$ be $\varepsilon$-far from monotone with $\varepsilon>0$. Then there exist a power of two $1\le d\le n$, a value $b\in\{0,1\}$ and a bipartite graph $G=(A,B,E)$ with
--   $$
--   A\subseteq f^{-1}(b),\qquad B\subseteq f^{-1}(1-b),\qquad E\subseteq E^-_f,
--   $$
--   such that $\deg_G(y)=d$ for every $y\in B$, $\deg_G(x)\le 2d$ for every $x\in A$, and
--   $$
--   \sigma=\frac{|B|}{2^n}\ge c\,\varepsilon\,d^{-5/8}.
--   $$
--   This adapts the degree-removal argument of [KMS18, Lemma 6.5] using Theorem 4; it supplies the scale $d$ at which the path tester finds violations.
--
--   Differences from the source:
--   - encoding: a power of two 1 ≤ d ≤ n; a bipartite graph G = (A, B, E) → d = 2^j with 2^j ≤ n; E a finite set of (lower, upper) pairs each with one endpoint in A and the other in B, degrees counted in E; reason: same objects
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), Lemma 5, p.11, eq. (12)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_IsMonoTester
import Definitions.Def_QCopyMono_ViolatedEdge

namespace QCopyMono

open QAlgorithms

/-- Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), Lemma 5, p.11 (adapted from [KMS18,
Lemma 6.5]): there is an absolute constant `c > 0` such that, for `n ≥ 1` and `f` `ε`-far from
monotone with `ε > 0`, there are a power of two `1 ≤ d ≤ n`, a value `b ∈ {0,1}` and a bipartite
graph `G = (A, B, E)` with `A ⊆ f⁻¹(b)`, `B ⊆ f⁻¹(1 − b)`, `E ⊆ E⁻_f`, `deg_G(y) = d` for every
`y ∈ B`, `deg_G(x) ≤ 2d` for every `x ∈ A`, and `σ = |B|/2ⁿ ≥ c ε d^{−5/8}` (eq. (12)).

**Formalization Note.** `d = 2^j`. An edge is stored as its (lower, upper) pair; "bipartite
graph `(A, B, E)`" is the clause that every edge has one endpoint in `A` and the other in `B`.
Degrees are counted in `E`. `1 − b` is `!b`. -/
theorem lemma_5 :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (f : Qubits n → Bool) (ε : ℝ), 0 < ε → IsFar ε f →
      ∃ (j : ℕ) (b : Bool) (A B : Finset (Qubits n)) (E : Finset (Qubits n × Qubits n)),
        2 ^ j ≤ n ∧
        (∀ x ∈ A, f x = b) ∧ (∀ y ∈ B, f y = !b) ∧
        (∀ e ∈ E, ViolatedEdge f e.1 e.2) ∧
        (∀ e ∈ E, (e.1 ∈ A ∧ e.2 ∈ B) ∨ (e.1 ∈ B ∧ e.2 ∈ A)) ∧
        (∀ y ∈ B, (E.filter fun e => e.1 = y ∨ e.2 = y).card = 2 ^ j) ∧
        (∀ x ∈ A, (E.filter fun e => e.1 = x ∨ e.2 = x).card ≤ 2 * 2 ^ j) ∧
        c * ε * ((2 : ℝ) ^ j) ^ (-(5 / 8 : ℝ)) ≤ (B.card : ℝ) / 2 ^ n := by sorry

end QCopyMono
