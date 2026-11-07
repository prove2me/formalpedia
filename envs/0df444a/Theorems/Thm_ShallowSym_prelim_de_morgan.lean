-- Prove2me | Theorems.Thm_ShallowSym_prelim_de_morgan
-- name    : ShallowSym.prelim_de_morgan
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:29.178128+00:00
-- url     : https://prove2.me/theorems/30c66cc8-3daf-425b-a0e4-c3344e757d26
-- title:
--   De Morgan: the negation of a $\Sigma_d$ formula is a $\Pi_d$ formula of the same size
-- statement:
--   For every depth $d$ and every depth-$d$ formula $\varphi$:
--
--   1. there is a $\Pi_d$ formula $\psi$ with $\mathrm{size}(\psi)=\mathrm{size}(\varphi)$ computing $\neg\varphi$, where $\varphi$ is read as a $\Sigma_d$ formula;
--   2. there is a $\Sigma_d$ formula $\psi$ with $\mathrm{size}(\psi)=\mathrm{size}(\varphi)$ computing $\neg\varphi$, where $\varphi$ is read as a $\Pi_d$ formula.
--
--   Since the negation of a symmetric function is symmetric, this reduces Theorem 1 to $\Sigma_d$ formulas.
--
--   **Formalization Note** Formulas are strictly layered alternating AND/OR trees over literals (`ShallowSym.Layer`): every literal sits at depth exactly $d$, a gate at level $\ell$ reads only nodes of level $\ell-1$, gates of arbitrary (also empty) fan-in, size = number of gates.
--
--   Differences from the source:
--   - reading: Σd and Πd circuits (DAGs) → Σd and Πd formulas (trees, ShallowSym.Layer); reason: the mission's circuit model is the formula model of Theorem 1, in which the whole proof runs; the De Morgan transformation maps formulas to formulas
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §2 'Circuits', p.5

import Mathlib
import Definitions.Def_ShallowSym_Layer

namespace ShallowSym

/-- §2 "Circuits", p.5. V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…).

"By De Morgan’s laws, the negation of a Σd circuit is a Πd circuit of the same size, and vice
versa."

For every depth `d` and every depth-`d` formula `φ`: there is a Π_d formula of the same size
computing the negation of the Σ_d formula `φ`, and there is a Σ_d formula of the same size
computing the negation of the Π_d formula `φ`.

**Formalization Note.** Stated for formulas (`Layer`); at `d = 0` a formula is a literal and the
claim is the negation of a literal. -/
theorem prelim_de_morgan (n d : ℕ) (φ : Layer n d) :
    (∃ ψ : Layer n d, size d ψ = size d φ ∧ ∀ x, evalPi d ψ x = !evalSigma d φ x) ∧
    (∃ ψ : Layer n d, size d ψ = size d φ ∧ ∀ x, evalSigma d ψ x = !evalPi d φ x) := by sorry

end ShallowSym
