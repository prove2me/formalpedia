-- Prove2me | Theorems.Thm_ShallowSym_prelim_collapse
-- name    : ShallowSym.prelim_collapse
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:39.532209+00:00
-- url     : https://prove2.me/theorems/61f6ff89-2070-4615-8904-4d84c32c2586
-- title:
--   Collapsing output gates: an OR of $\Sigma_m$ formulas is a $\Sigma_m$ formula, an AND of $\Pi_m$ formulas is a $\Pi_m$ formula
-- statement:
--   Let $m\ge 1$ and let $\varphi_1,\dots,\varphi_r$ be depth-$m$ formulas. Then
--
--   1. the function $x\mapsto \bigvee_{i=1}^r \varphi_i(x)$, with each $\varphi_i$ read as a $\Sigma_m$ formula, is computed by a single $\Sigma_m$ formula with at most $1+\sum_{i}\mathrm{size}(\varphi_i)$ gates;
--   2. the function $x\mapsto \bigwedge_{i=1}^r \varphi_i(x)$, with each $\varphi_i$ read as a $\Pi_m$ formula, is computed by a single $\Pi_m$ formula with at most $1+\sum_{i}\mathrm{size}(\varphi_i)$ gates.
--
--   This is how the paper combines the circuits of the decomposition (1) under one output OR (p.5) and the tests of the moduli $k_1,\dots,k_{d-1}$ under one output AND (p.11) without increasing the depth.
--
--   **Formalization Note** Formulas are strictly layered alternating AND/OR trees over literals (`ShallowSym.Layer`): every literal sits at depth exactly $d$, a gate at level $\ell$ reads only nodes of level $\ell-1$, gates of arbitrary (also empty) fan-in, size = number of gates.
--
--   Differences from the source:
--   - generalization: level d (p.5, output OR) and level d − 1 (p.11, output AND) → any level m ≥ 1, both the OR and the AND version; reason: specializes to m = d and m = d − 1
--   - encoding: 'without increasing the depth', size 2^{O(n^{1/(d−1)})} (no explicit count) → explicit size bound 1 + Σ size φᵢ; reason: the paper's asymptotic size follows from the explicit count; same instances
--   - reading: circuits → formulas (ShallowSym.Layer); reason: the mission's circuit model is the formula model of Theorem 1
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §2 'Circuits', p.5; §4 'Anatomy of a test', p.11

import Mathlib
import Definitions.Def_ShallowSym_Layer

namespace ShallowSym

/-- §2 "Circuits", p.5 and §4, p.11: collapsing output gates. V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…).

p.5: "We focus on Σd circuits, whose output OR lets us combine the circuits in the decomposition
by weight in Equation (1) without increasing the depth." p.11: "Ultimately, the test for |x| = t
is the AND of polynomially many circuits of this size. We can collapse their output AND gates, so
the overall test is implemented as a Πd−1 circuit of size 2^{O(n^{1/(d−1)})}."

For `m ≥ 1` and finitely many depth-`m` formulas `φ_1, …, φ_r`: the OR of the Σ_m formulas
`φ_i` is computed by a single Σ_m formula with at most `1 + ∑ size φ_i` gates, and the AND of the
Π_m formulas `φ_i` by a single Π_m formula with at most `1 + ∑ size φ_i` gates.

**Formalization Note.** A general level `m ≥ 1` covers both uses (`m = d` on p.5, `m = d − 1`
on p.11). For `r = 0` the combined formula is an empty gate (size 1). -/
theorem prelim_collapse (n m : ℕ) (hm : 1 ≤ m) (r : ℕ) (φ : Fin r → Layer n m) :
    (∃ ψ : Layer n m, (∀ x, evalSigma m ψ x = decide (∃ i, evalSigma m (φ i) x = true)) ∧
      size m ψ ≤ 1 + ∑ i, size m (φ i)) ∧
    (∃ ψ : Layer n m, (∀ x, evalPi m ψ x = decide (∀ i, evalPi m (φ i) x = true)) ∧
      size m ψ ≤ 1 + ∑ i, size m (φ i)) := by sorry

end ShallowSym
