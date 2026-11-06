-- Prove2me | Theorems.Thm_TransvectionMixing_proposition_6_2_single_entry
-- name    : TransvectionMixing.proposition_6_2_single_entry
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:21:43.062728+00:00
-- url     : https://prove2.me/theorems/536dbc3d-c4d0-4f00-8b10-471ff2029720
-- title:
--   Proposition 6.2 — single-entry lower bounds on $d_{\mathcal S}(t)$
-- statement:
--   Let $n\ge 2$ and $q=|\mathbb F_q|$. For every nonempty $\mathcal S\subseteq[n]\times[n]$ and integer $t\ge 0$,
--   $$
--   d_{\mathcal S}(t)\ \ge\ 1-\frac{q^{n-1}-1}{q^n-1}-\frac{e^{t/n}-1}{n-1}
--   \qquad\text{and}\qquad
--   d_{\mathcal S}(t)\ \ge\ \frac12\Bigl(1-\frac1n\Bigr)^t .
--   $$
--
--   These are the propagation obstructions behind the $n\log(n/\varepsilon)$ term of the lower bound.
--
--   Differences from the source:
--   - encoding: the walk on n rows (the paper's results take n ≥ 2 implicitly: a step needs two distinct rows) → hypothesis 2 ≤ n; reason: excludes only n ≤ 1, where no skeleton of positive length exists
--   - encoding: laws of the walk over uniform skeletons and uniform coefficients → normalized counts (`prob`, `skelLaw`, `entryLaw`, `piS`) over finite types; reason: Lean convention for finite uniform probability; same values
--   - encoding: ‖·‖_TV → the published `MarkovMixing.tvDist` (max over events of |μ(A) − ν(A)|); reason: equals ½∑|μ − ν| on probability vectors; same values
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Proposition 6.2, eqs. (45)–(46), p.34

import Mathlib
import Definitions.Def_TransvectionMixing_dS

namespace TransvectionMixing

/-- **Proposition 6.2** (a single entry) (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §6.2, p.34). Write `q = |𝔽_q|`. For every
nonempty `𝒮 ⊆ [n] × [n]` and integer `t ≥ 0`,
`d_𝒮(t) ≥ 1 − (q^{n−1} − 1)/(q^n − 1) − (e^{t/n} − 1)/(n − 1)` (eq. (45)) and
`d_𝒮(t) ≥ ½(1 − 1/n)^t` (eq. (46)).

**Formalization Note** `n ≥ 2` (the walk needs two distinct rows). -/
theorem proposition_6_2_single_entry (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) (hn : 2 ≤ n) (S : Finset (Fin n × Fin n)) (hS : S.Nonempty) (t : ℕ) :
    1 - ((Fintype.card F : ℝ) ^ (n - 1) - 1) / ((Fintype.card F : ℝ) ^ n - 1)
        - (Real.exp (t / n) - 1) / ((n : ℝ) - 1) ≤ dS F S t ∧
      1 / 2 * (1 - 1 / (n : ℝ)) ^ t ≤ dS F S t := by sorry

end TransvectionMixing
