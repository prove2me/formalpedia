-- Prove2me | Theorems.Thm_SaglamGV_main_theorem
-- name    : SaglamGV.main_theorem
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:47:50.748108+00:00
-- url     : https://prove2.me/theorems/d11d197e-c04f-4087-9358-8a55b5ec493a
-- title:
--   Main theorem: binary linear codes of distance $d$ and size $c_\varepsilon n2^n/\sum_{i=1}^{d-1}\binom ni$ for $\lg n\ll d\le(1/2-\varepsilon)n$
-- statement:
--   Fix $\varepsilon>0$ and let $n,d$ satisfy $\lg n\ll d\le(1/2-\varepsilon)n$. Then there exist binary linear codes $C\subseteq\mathbb F_2^n$ of distance $d$ and size
--
--   $$
--   |C|\ge c_\varepsilon\,n\,\frac{2^n}{\sum_{i=1}^{d-1}\binom ni}
--   $$
--
--   for some $c_\varepsilon>0$ depending on $\varepsilon$ only.
--
--   Precisely: for every $\varepsilon>0$ there are $c>0$, $L$ and $N_0$, depending only on $\varepsilon$, such that for every $n\ge N_0$ and every $d$ with $L\lg n\le d\le(1/2-\varepsilon)n$ there is a subspace $C\subseteq\mathbb F_2^n$ in which every nonzero vector has Hamming weight at least $d$ and $|C|\ge c\,n\,2^n/\sum_{i=1}^{d-1}\binom ni$.
--
--   The Gilbert–Varshamov bound gives linear codes of size $2^n/(V+1)$ with $V=\sum_{i=1}^{d-1}\binom ni$; the theorem improves it by a factor $\Omega(n)$, uniformly over the whole range of distances.
--
--   Differences from the source:
--   - encoding: lg n ≪ d (with the code existing for the stated n, d) → ∃ L, N₀ depending on ε only (after c), for all n ≥ N₀ and L·lg n ≤ d ≤ (1/2 − ε)n; reason: equivalent to the sequential reading: if it failed for every L, N₀, one could pick n_k ≥ k and d_k ≥ k·lg n_k violating it, a sequence with d/lg n → ∞
--   - encoding: a code of distance d → a subspace in which every nonzero codeword has weight ≥ d (HasDistAtLeast); reason: the paper's definition on p.1 (Hx ≠ 0 for all x ∈ B_d); for linear codes minimum distance = minimum nonzero weight
--   - encoding: linear codes over 𝔽₂ⁿ and their size → Submodule (ZMod 2) (Fin n → ZMod 2) and Nat.card; reason: Lean representation; same objects
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), Main theorem (Abstract, p.1); restated in §1, p.1; proved in §§2–3, pp.2–5

import Mathlib
import Definitions.Def_SaglamGV_Code

namespace SaglamGV

/-- Main theorem (M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript (held version, sha256 ac6f2bba…), Abstract, p.1: "Fix ϵ > 0, and let n, d satisfy lg n ≪ d ≤ (1/2 − ϵ)n. We show
the existence of linear codes over F_2^n of distance d and size at least c_ϵ n 2^n / Σ_{i=1}^{d−1} (n choose i)
for some c_ϵ > 0 depending on ϵ only").

For every $ε > 0$ there are $c > 0$, $L$ and $N_0$ (depending on $ε$ only) such that for every
$n ≥ N_0$ and every $d$ with $L\lg n ≤ d ≤ (1/2 − ε)n$ there is a binary linear code
$C ⊆ 𝔽_2^n$ in which every nonzero codeword has weight at least $d$ and
$|C| ≥ c\, n\, 2^n / \sum_{i=1}^{d−1}\binom{n}{i}$.

**Formalization Note** "$\lg n ≪ d$" is encoded uniformly as $∃ L, N_0$ after $c$ (equivalent to the
sequential reading: for every sequence with $d/\lg n → ∞$ the codes exist for all large $n$).
"Distance $d$" is the paper's p.1 notion, minimum distance at least $d$. Codes are subspaces
`Submodule (ZMod 2) (Fin n → ZMod 2)` and $|C|$ is `Nat.card`. -/
theorem main_theorem (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, ∃ N₀ : ℕ, ∀ n d : ℕ, N₀ ≤ n → L * Real.logb 2 n ≤ d →
      (d : ℝ) ≤ (1 / 2 - ε) * n →
      ∃ C : Submodule (ZMod 2) (Fin n → ZMod 2), HasDistAtLeast C d ∧
        c * n * (2 : ℝ) ^ n / (∑ i ∈ Finset.Icc 1 (d - 1), (n.choose i : ℝ)) ≤ Nat.card C := by sorry

end SaglamGV
