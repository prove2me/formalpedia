-- Prove2me | Theorems.Thm_ReconfRes_Frozen_lemma_3_8
-- name    : ReconfRes.Frozen.lemma_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:21:40.956895+00:00
-- url     : https://prove2.me/theorems/f014250c-5ac9-444d-8f97-d0081fcd083a
-- title:
--   Lemma 3.8 — a lean refutation with α axiom nodes has ρ = α − 1 + X resolution nodes and |R| = 2α − 1 + X + ω ≥ 2α − 1
-- statement:
--   Let $R$ be a lean refutation (of some formula $F$) with $\alpha$ axiom nodes, $\rho$ resolution nodes and $\omega$ weakening nodes, and let $X$ be the sum, over all nodes other than the sink, of their number of consumers minus one. Then
--   $$X\ge0,\qquad \rho=\alpha-1+X,\qquad |R|=2\alpha-1+X+\omega,\qquad\text{in particular } |R|\ge2\alpha-1 .$$
--   The identity is what makes the budget $2\alpha-1$ the minimum size for $\alpha$ prescribed axiom occurrences.
--
--   Differences from the source:
--   - encoding: α, ρ, ω, X and the identities over the integers → the counts as integers (ℤ); node kinds as nodes with 0, 2 and 1 parents; reason: no truncated subtraction; kinds are determined by the number of parents in Definition 2.1
-- source:
--   Myrisiotis, Reconfiguring Resolution Refutations, STOC 2027 submission (manuscript sha256 8b5124c1…), p. 25, Lemma 3.8

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_ReconfRes_Frozen_Refutation

open MultiplierAssoc206.Resolution

namespace ReconfRes.Frozen

/-- **Lemma 3.8** (lean refutations have few axiom nodes). For a lean refutation `R` with `α`
axiom nodes, `ρ` resolution nodes and `ω` weakening nodes, and `X` the sum over the non-sink nodes
of (number of consumers − 1): `X ≥ 0`, `ρ = α − 1 + X`, `|R| = 2α − 1 + X + ω`, hence
`|R| ≥ 2α − 1`. -/
theorem lemma_3_8 {V : Type} [DecidableEq V] (F : CNF V) (R : ProofDag V)
    (hR : R.IsRefutationOf F) (hlean : R.IsLean) :
    let α : ℤ := ((Finset.univ.filter fun i => R.parents i = ∅).card : ℤ)
    let ρ : ℤ := ((Finset.univ.filter fun i => (R.parents i).card = 2).card : ℤ)
    let ω : ℤ := ((Finset.univ.filter fun i => (R.parents i).card = 1).card : ℤ)
    let X : ℤ := ∑ i ∈ Finset.univ.filter (fun i => i ≠ R.sink), (((R.consumers i).card : ℤ) - 1)
    0 ≤ X ∧ ρ = α - 1 + X ∧ (R.size : ℤ) = 2 * α - 1 + X + ω ∧ 2 * α - 1 ≤ (R.size : ℤ) := by sorry

end ReconfRes.Frozen
