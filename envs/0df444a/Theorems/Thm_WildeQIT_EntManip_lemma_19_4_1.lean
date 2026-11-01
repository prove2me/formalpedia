-- Prove2me | Theorems.Thm_WildeQIT_EntManip_lemma_19_4_1
-- name    : WildeQIT.EntManip.lemma_19_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:27.303954+00:00
-- url     : https://prove2.me/theorems/cbc9de69-aa09-4f28-b06e-5e581c17930f
-- title:
--   Lemma 19.4.1 (Hashing): a one-to-one $g$ with $\frac12\|p_{W_l}\times p_{W_r}-p_{g(W_k)}\|_1\le l/k$
-- statement:
--   Let $k$ and $l$ be positive integers with $k\ge l$, and let $r=\lceil k/l\rceil$. Let $W_k$, $W_l$, $W_r$ be uniformly distributed on $\{1,\dots,k\}$, $\{1,\dots,l\}$ and $\{1,\dots,r\}$ respectively. Then there exists a one-to-one function
--
--   $$
--   g:\{1,\dots,k\}\to\{1,\dots,l\}\times\{1,\dots,r\}
--   $$
--
--   such that
--
--   $$
--   \frac12\left\|p_{W_l}\times p_{W_r}-p_{g(W_k)}\right\|_1\le\frac lk .
--   $$
--
--   The lemma hashes a uniform random variable on a large set onto a product of a smaller uniform register and a remainder register, at small cost in trace distance; it is the classical core of randomness and entanglement concentration.
--
--   **Formalization Note** The sets are `Fin k`, `Fin l`, `Fin r` (0-based), with $r=\lceil k/l\rceil$ as a natural-number ceiling. The product distribution is the constant $\frac1l\cdot\frac1r$, and $p_{g(W_k)}(z)=\sum_{w:\,g(w)=z}\frac1k$ is the law of $g(W_k)$. $\|\cdot\|_1$ is the published `WildeQIT.classicalTraceDist`. Positivity of $k$ is not a separate hypothesis, as it follows from $0<l\le k$.
--
--   Differences from the source:
--   - encoding: {1, …, k}, {1, …, l}, {1, …, r} → Fin k, Fin l, Fin r (0-based); reason: relabelling; same instances
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 19.4.1 (Hashing), (19.70), p. 544

import Mathlib
import Definitions.Def_WildeQIT_classicalTraceDist

namespace WildeQIT.EntManip

/-- **Lemma 19.4.1 (Hashing)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, p. 544): "Let `k` and `l` be positive integers such that `k ≥ l`. Let `W_k` be
uniformly distributed on the set `{1, …, k}`, `W_l` be uniformly distributed on the set
`{1, …, l}`, and `W_r` be uniformly distributed on the set `{1, …, r = ⌈k/l⌉}`. Then there exists a
one-to-one function `g : {1, …, k} → {1, …, l} × {1, …, r}` such that
`(1/2)‖p_{W_l} × p_{W_r} − p_{g(W_k)}‖₁ ≤ l/k`." (19.70)

**Formalization Note** `{1, …, k}` is `Fin k` (0-based), `r = ⌈k/l⌉₊`. The product distribution
`p_{W_l} × p_{W_r}` is the constant `(1/l)(1/r)`; the law of `g(W_k)` is the pushforward
`p_{g(W_k)}(z) = ∑_{w : g w = z} 1/k`. `‖·‖₁` is the published `WildeQIT.classicalTraceDist`.
`k > 0` follows from `0 < l ≤ k`. -/
theorem lemma_19_4_1 (k l : ℕ) (hl : 0 < l) (hlk : l ≤ k) :
    ∃ g : Fin k → Fin l × Fin ⌈(k : ℝ) / l⌉₊, Function.Injective g ∧
      (1 / 2 : ℝ) * WildeQIT.classicalTraceDist
        (fun _ => (1 / (l : ℝ)) * (1 / (⌈(k : ℝ) / l⌉₊ : ℝ)))
        (fun z => ∑ w ∈ Finset.univ.filter (fun w => g w = z), (1 / (k : ℝ)))
        ≤ (l : ℝ) / k := by sorry

end WildeQIT.EntManip
