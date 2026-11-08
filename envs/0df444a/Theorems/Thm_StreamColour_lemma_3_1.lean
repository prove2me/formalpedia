-- Prove2me | Theorems.Thm_StreamColour_lemma_3_1
-- name    : StreamColour.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:52:58.152238+00:00
-- url     : https://prove2.me/theorems/a65b413a-a603-493c-9748-c3ab38726535
-- title:
--   Lemma 3.1 — lists of size $\ge d_H(v)+1$ and $\ge\alpha q$: $O(\ell^2)$ sampled colours suffice
-- statement:
--   Fix constants $\alpha\in(0,1]$ and $c>0$. Let $H$ have at most $n$ vertices, with fixed lists $L(v)\subseteq[q]$ satisfying $|L(v)|\ge d_H(v)+1$ and $|L(v)|\ge\alpha q$. Independently at every vertex, sample a uniform $t$-element set $P(v)\subseteq[q]$, where $t=\min\{q,\lceil C_{\alpha,c}\ell^2\rceil\}$. For sufficiently large $C_{\alpha,c}$, with probability at least $1-n^{-c}$ there is a proper colouring of $H$ from $L(v)\cap P(v)$.
--
--   This is the consequence of degree-plus-one palette sparsification used to complete a partial colouring from samples drawn before the lists are known. $\ell$ is computed from $n$, not from the number of vertices of $H$.
--
--   Differences from the source:
--   - encoding: independent uniform $t$-subsets, and "sufficiently large $C_{\alpha,c}$" → the uniform law on the product of $t$-subset types, with a threshold $C_0$ depending only on $\alpha,c$; reason: a product of uniform laws is the uniform law on the product
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Lemma 3.1, p.21 (PDF 23)

import Mathlib
import Definitions.Def_StreamColour_Params
import Definitions.Def_StreamColour_GraphQuantities

namespace StreamColour

/-- Chakraborty, Chatterjee, Kundu, Mishra, *Streaming Graph Colouring Meets Molloy–Reed via Kernelization* (STOC 2027 submission, sha256 31a813b3…), Lemma 3.1, p.21 (PDF 23).

**Formalization Note.** `ℓ` is of `n`, not of `|V|`. The law is uniform on the product of the `t`-subset types, i.e. `P(v)` is independent and
uniform at every vertex. `|L(v)| ≥ αq` is real. There is no hypothesis on the maximum degree. `C₀` depends only on `α` and `c`, before the
graph. `n^{-c}` is `Real.rpow`, and `c` is any positive real; at `n = 0` the vertex set is empty and the probability is `1`. -/
theorem lemma_3_1 : ∀ α c : ℝ, 0 < α → α ≤ 1 → 0 < c → ∃ C₀ : ℝ, ∀ Cac ≥ C₀, ∀ (n q : ℕ) (V : Type) [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (L : V → Finset (Fin q)),
    Fintype.card V ≤ n →
    (∀ v, dG H v + 1 ≤ (L v).card) → (∀ v, α * (q : ℝ) ≤ ((L v).card : ℝ)) →
    1 - (n : ℝ) ^ (-c) ≤ unifProb (V → TSubset q (min q (sampleSize Cac n)))
      (fun P => ∃ φ : V → Fin q, (∀ u v, H.Adj u v → φ u ≠ φ v) ∧
        ∀ v, φ v ∈ L v ∧ φ v ∈ (P v).1) := by sorry

end StreamColour
