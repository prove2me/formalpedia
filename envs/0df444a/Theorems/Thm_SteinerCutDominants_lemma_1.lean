-- Prove2me | Theorems.Thm_SteinerCutDominants_lemma_1
-- name    : SteinerCutDominants.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:16:20.444469+00:00
-- url     : https://prove2.me/theorems/59f37885-9f7f-4424-9e8d-a923f657125e
-- title:
--   Lemma 1: $|\mathcal L|\le|V|+|\mathcal L_{\min}|-1$ for laminar families
-- statement:
--   Let $V\neq\emptyset$ be finite and $\mathcal L$ a laminar family of distinct nonempty subsets of $V$. Then
--   $$
--   |\mathcal L|\le|V|+|\mathcal L_{\min}|-1 .
--   $$
--   With the laminar root basis of Theorem 1, this yields the bound on the number of edges of an irreducible Steiner graph in Lemma 6.
--
--   Differences from the source:
--   - encoding: |L| ≤ |V| + |L_min| − 1 → L.card + 1 ≤ card V + (lminOf L).card; reason: no natural-number subtraction
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, Lemma 1, p.6

import Mathlib
import Definitions.Def_SteinerCutDominants_IsLaminar
import Definitions.Def_SteinerCutDominants_lminOf

namespace SteinerCutDominants

/-- **Lemma 1** (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, p.6). Every laminar
family `𝓛` of distinct nonempty subsets of `V ≠ ∅` satisfies `|𝓛| ≤ |V| + |𝓛_min| - 1`.

**Formalization Note** Written `|𝓛| + 1 ≤ |V| + |𝓛_min|`, with no natural-number subtraction. -/
theorem lemma_1 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (L : Finset (Finset V))
    (hL : IsLaminar L) (hne : ∅ ∉ L) :
    L.card + 1 ≤ Fintype.card V + (lminOf L).card := by sorry

end SteinerCutDominants
