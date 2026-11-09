-- Prove2me | Theorems.Thm_TermCycDich_theorem_1_3
-- name    : TermCycDich.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:46:29.416146+00:00
-- url     : https://prove2.me/theorems/66342ceb-fb70-45db-949e-f782ef97a24c
-- title:
--   Theorem 1.3 — vital instances have treewidth $\mathrm{poly}(\mathrm{bidim})\cdot\log|G|$
-- statement:
--   There exists a function $\beta:\mathbb N^2\to\mathbb N$ with $\beta(b,n)\in\mathrm{poly}(b)\cdot\log n$ such that for every vital instance $(G,R)$ of Terminal Cyclability
--
--   $$
--   \mathrm{tw}(G)\le\beta\bigl(\mathrm{bidim}(G,R),|G|\bigr).
--   $$
--
--   Vital instances are those with a unique $R$-cycle through all vertices; the bound is the base case of the weak irrelevant vertex rule (Theorem 1.2).
--
--   Differences from the source:
--   - reading: β(b, |G|) ∈ poly(b) · log |G| → there is a polynomial p with natural coefficients such that β(b, n) ≤ p(b) · ln n for all b and all n ≥ 3; reason: the proof states the bound for n ≥ 3 (p.32) and vital instances have |G| ≥ 3; the log base is absorbed into p
--   - encoding: graphs G and tw(G) ≤ k → any finite vertex type V; the public RobertsonSeymour1986.GM5.TreewidthLE; reason: Lean convention; same instances
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Theorem 1.3, p.10 (PDF 12), restated p.32 (PDF 34)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Definitions.Def_TermCycDich_IsVital
import Definitions.Def_TermCycDich_bidim

namespace TermCycDich

/-- **Theorem 1.3.** There is a function `β : ℕ² → ℕ` with `β(b, n) ∈ poly(b) · log n` such that
every vital instance `(G, R)` has `tw(G) ≤ β(bidim(G, R), |G|)`.

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Theorem 1.3, p.10 (PDF 12), restated p.32 (PDF 34); the proof (p.32) gives "For n ≥ 3,
this gives β(b, n) ∈ poly(b) · log n".

**Formalization Note** "`β(b, n) ∈ poly(b) · log n`" is: some polynomial `p` with natural
coefficients has `β(b, n) ≤ p(b) · ln n` for all `b` and all `n ≥ 3` (vital instances have
`|G| ≥ 3`; the log base is absorbed into `p`). Tree-width is the public
`RobertsonSeymour1986.GM5.TreewidthLE`. -/
theorem theorem_1_3 :
    ∃ β : ℕ → ℕ → ℕ,
      (∃ p : Polynomial ℕ, ∀ b n : ℕ, 3 ≤ n → (β b n : ℝ) ≤ ((p.eval b : ℕ) : ℝ) * Real.log n) ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (R : Set V), IsVital G R →
        RobertsonSeymour1986.GM5.TreewidthLE G (β (bidim G R) (Fintype.card V)) := by sorry

end TermCycDich
