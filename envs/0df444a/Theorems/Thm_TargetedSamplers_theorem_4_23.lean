-- Prove2me | Theorems.Thm_TargetedSamplers_theorem_4_23
-- name    : TargetedSamplers.theorem_4_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:08:35.106419+00:00
-- url     : https://prove2.me/theorems/5feb4740-007c-4419-bc0f-49ce389367aa
-- title:
--   Theorem 4.23 — bootstrapping system with block locality
-- statement:
--   Let $d,T,\ell:\mathbb N\to\mathbb N$ be time-constructible, $T(n)$ always a power of $2$ and $T(n)\ge n$. Let $\{C_n\}$ be a sufficiently uniform circuit family of width $T(n)$, depth $d(n)$ and output length $\ell$ that computes $f$. Then there are $d'(n)\le K\,(d(n)+1)\,(\log_2T(n)+1)^2$ and strings
--   $$B_1(x),\dots,B_{d'+1}(x)\in[A]^{T'},\qquad A=T'=2T,$$
--   that form a $(d'\times T')$ bootstrapping system for $f$, with the five properties: input layer, downward self-reducibility, batch computability, output layer and block locality with at most $5$ blocks.
--
--   This is the encoding the targeted generator of Proposition 4.26 prints and reconstructs.
--
--   Differences from the source:
--   - encoding: d′ = O(d · log² T) → d′(n) ≤ K·(d(n)+1)·(log₂ T(n)+1)²; reason: O(·) of a quantity that vanishes at d = 0 or T = 1, where the construction still has 2(d+1) layers
--   - reading: item 3: (1ⁿ, i) ∈ {1ⁿ} × [d′+1] → 2 ≤ i ≤ d′+1; reason: B₀ does not exist; the proof uses i ≥ 2
--   - reading: item 4: for every i ∈ [n] → for every i ∈ [ℓ(n)]; reason: f(x)ᵢ is defined only for i ≤ ℓ(n); for ℓ = n the two agree
--   - reading: item 5: the positions queried "when we apply the DSR algorithm to compute all of the entries in the block" → the positions queried for every entry of the block and every witness w, covered by at most 5 blocks of index < ⌈T′/s⌉, for every s ≥ 1; reason: the queries do not depend on the witness in the construction; quantifying over all witnesses is the stronger reading
--   - reading: connectivity: the direct connection language of footnote 29 (in-edges) → the out-edge relation OUTᵢ(g, b) = g′, decided from (i, g, b, g′, n); reason: the proof queries ⟨g, g′, b, 1ⁿ⟩ for OUTᵢ(g, b) = g′ (p.33)
--   - reading: layer 1 "provides access to all literals" → layer 1 is x₀,…,x_{n−1}, ¬x₀,…,¬x_{n−1}, then 0; reason: a fixed layout is needed for the O(log T) input-layer algorithm; the proof pads with 0
--   - encoding: algorithms with several arguments and outputs in [A] → arguments encoded by encInput; outputs in binary (layers in fixed width log₂ 2T); reason: the page fixes no encoding
--   - reading: O(log T), polylog(T), Õ(·) → budget(log T), K·(log₂ T + 1)^k, budget; reason: time on the log-cost RAM up to polylogarithmic factors
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorem 4.23, pp.30–31 (pdf pp.32–33)

import Mathlib
import Definitions.Def_TargetedSamplers_IsSufficientlyUniform
import Definitions.Def_TargetedSamplers_IsBootstrappingSystem

namespace TargetedSamplers

/-- Theorem 4.23 (bootstrapping system with block locality) (Chen, Doron, Ebtehaj, Tell, Targeted
Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, pp.30–31). Let `d, T, ℓ : ℕ → ℕ` be
time-constructible, `T(n)` always a power of 2 and `T(n) ≥ n`. Let `C = {C_n}` be a sufficiently
uniform circuit family of width `T(n)`, depth `d(n)` and output length `ℓ`, computing `f`. Then for
every `x` there is a sequence `B₁(x), …, B_{d′+1}(x) ∈ [A]^{T′}`, `A = 2T`, `d′ = O(d · log² T)`,
`T′ = 2T`, with the five properties (Input Layer, Downward self-reducibility, Batch-computability,
Output Layer, Block Locality) of a `(d′ × T′)` bootstrapping system.

**Formalization Note** The five properties are `IsBootstrappingSystem` (readings there).
`d′ = O(d · log² T)` is `d′(n) ≤ K · (d(n) + 1) · (log₂ T(n) + 1)²`; the `+ 1`s keep the bound
meaningful at `d = 0` or `T = 1`, where the page's construction still has `2(d + 1)` layers. -/
theorem theorem_4_23 (d T ℓ : ℕ → ℕ) (hd : TimeConstructible d) (hT : TimeConstructible T)
    (hℓ : TimeConstructible ℓ) (hT2 : ∀ n, ∃ e : ℕ, T n = 2 ^ e) (hTn : ∀ n, n ≤ T n)
    (F : (n : ℕ) → LayeredCircuit n) (hF : IsSufficientlyUniform F d T ℓ)
    (f : List Bool → List Bool) (hf : Computes F f) :
    ∃ (d' : ℕ → ℕ) (B : List Bool → ℕ → ℕ → ℕ),
      (∃ K : ℕ, ∀ n, d' n ≤ K * (d n + 1) * (Nat.log 2 (T n) + 1) ^ 2) ∧
      IsBootstrappingSystem d T ℓ f d' B := by sorry

end TargetedSamplers
