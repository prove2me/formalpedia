-- Prove2me | Theorems.Thm_TargetedSamplers_lemma_4_25
-- name    : TargetedSamplers.lemma_4_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:08:31.609748+00:00
-- url     : https://prove2.me/theorems/490324c2-4938-4d95-b2fa-56c01d97b0d8
-- title:
--   Lemma 4.25 — the original layers simulate the circuit
-- statement:
--   Let $C_n$ be a layered circuit of width $T$, a power of $2$, with fan-in $2$ in every layer after the first. For every input $x$, every $i\in[d+1]$, $g\in\{0,\dots,T-1\}$ and $b\in\{0,1\}$,
--   $$(P_i)_{g\circ b}=\text{the value of gate }g\text{ in the }i\text{th layer of }C_n,$$
--   where $P_i$ are the original layers of the bootstrapping construction and $g\circ b=2g+b$.
--
--   With $i=d+1$ this gives the output-layer property of Theorem 4.23.
--
--   Differences from the source:
--   - generalization: Cₙ in a sufficiently uniform family → every well-formed layered circuit whose width is a power of 2; reason: the proof uses only the circuit structure; every circuit of such a family is an instance
--   - reading: layer 1 "provides access to all literals" → layer 1 is x₀,…,x_{n−1}, ¬x₀,…,¬x_{n−1}, then 0; reason: the layout of the LayeredCircuit definition; P₁ replicates layer 1 whatever its layout
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Lemma 4.25, p.34 (pdf p.36)

import Mathlib
import Definitions.Def_TargetedSamplers_origLayer

namespace TargetedSamplers

/-- Lemma 4.25 (Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission, manuscript
sha256 599d0a59…, p.34). For every `i ∈ [d + 1]`, `g ∈ {0, …, T − 1}` and `b ∈ {0,1}`, the value of
`(Pᵢ)_{g∘b}` is the value of gate `g` in the `i`th layer of `C_n`.

**Formalization Note** `Pᵢ` is `LayeredCircuit.origLayer` (the construction of p.31–32) and
`g∘b = 2g + b`. Stated for every circuit with the structure of Definition 4.17 (fan-in 2, width a
power of 2), which includes every circuit of a sufficiently uniform family. -/
theorem lemma_4_25 {n : ℕ} (c : LayeredCircuit n) (hc : c.WellFormed)
    (hw : ∃ e : ℕ, c.width = 2 ^ e) (x : Fin n → Bool) :
    ∀ i : ℕ, 1 ≤ i → i ≤ c.depth + 1 → ∀ (g : Fin c.width) (b : Bool),
      c.origLayer x i (2 * g + b.toNat) = c.value x i g := by sorry

end TargetedSamplers
