-- Prove2me | Theorems.Thm_ShallowSym_prelim_cnf_dnf
-- name    : ShallowSym.prelim_cnf_dnf
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:09.06748+00:00
-- url     : https://prove2.me/theorems/f964c5c7-c9cb-475b-aa00-b9dc2b13246d
-- title:
--   Every Boolean function has a DNF and a CNF with at most $2^n+1$ gates
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$ be any Boolean function. Then $f$ is computed by a $\Sigma_2$ formula (a DNF) and by a $\Pi_2$ formula (a CNF), each with at most
--
--   $$2^n + 1$$
--
--   AND/OR gates.
--
--   This is the base case $d=2$ of the induction proving Theorem 1 ("$\Pi_2$ and $\Sigma_2$ circuits of size $2^n+1$", p.10), and it is used for small juntas throughout the paper.
--
--   **Formalization Note** Formulas are strictly layered alternating AND/OR trees over literals (`ShallowSym.Layer`): every literal sits at depth exactly $d$, a gate at level $\ell$ reads only nodes of level $\ell-1$, gates of arbitrary (also empty) fan-in, size = number of gates.
--
--   Differences from the source:
--   - encoding: size of a CNF/DNF = number of clauses or terms, bound 2ⁿ (p.5) → size = number of gates including the output gate, bound 2ⁿ + 1; reason: the proof of Theorem 1 (p.10) states the same fact in gate counts, 'Π2 and Σ2 circuits of size 2^n + 1'; the two conventions differ by exactly the output gate
--   - encoding: CNF/DNF (no statement about empty clause lists) → empty gates allowed (empty OR = false, empty AND = true); reason: the paper's DNF of the constant-0 function is the OR over no satisfying assignments; same instances
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §2 'Circuits', p.5; used as the base case of Theorem 1, p.10

import Mathlib
import Definitions.Def_ShallowSym_Layer

namespace ShallowSym

/-- §2 "Circuits", p.5, used as the base case `d = 2` of Theorem 1 (p.10). V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…).

"A useful fact is that every Boolean function on n variables can be represented as both a CNF
and a DNF of size at most 2^n." The proof of Theorem 1 (p.10) uses it with gates counted: "any
function can be represented as a CNF or DNF of size 2^n (Π2 and Σ2 circuits of size 2^n + 1)."

Every `f : {0,1}^n → {0,1}` is computed by a Σ_2 formula (DNF) and by a Π_2 formula (CNF), each
with at most `2^n + 1` gates.

**Formalization Note.** The p.5 convention counts clauses or terms; `size` counts every gate,
including the output gate, hence the bound `2^n + 1`. -/
theorem prelim_cnf_dnf (n : ℕ) (f : Cube n → Bool) :
    (∃ φ : Layer n 2, (∀ x, evalSigma 2 φ x = f x) ∧ size 2 φ ≤ 2 ^ n + 1) ∧
    (∃ ψ : Layer n 2, (∀ x, evalPi 2 ψ x = f x) ∧ size 2 ψ ≤ 2 ^ n + 1) := by sorry

end ShallowSym
