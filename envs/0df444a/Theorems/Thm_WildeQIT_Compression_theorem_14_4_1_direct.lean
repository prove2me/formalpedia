-- Prove2me | Theorems.Thm_WildeQIT_Compression_theorem_14_4_1_direct
-- name    : WildeQIT.Compression.theorem_14_4_1_direct
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:31.881182+00:00
-- url     : https://prove2.me/theorems/b4e48b16-91c2-4353-a58c-01e4fd6392b9
-- title:
--   Theorem 14.4.1, direct coding theorem: the entropy $H(X)$ is an achievable compression rate
-- statement:
--   Let $X$ be a discrete random variable with distribution $p_X$ on a finite alphabet $\mathcal X$ and entropy $H(X)$ in bits, and consider the i.i.d. source $X^n$. An $(n,R,\varepsilon)$ source code consists of an encoder $\mathcal E$ from $\mathcal X^n$ into a set of at most $2^{nR}$ codewords and a decoder $\mathcal D$ back to $\mathcal X^n$ with error probability $\Pr\{(\mathcal D\circ\mathcal E)(X^n)\neq X^n\}\le\varepsilon$. A rate $R$ is achievable for $X$ if there exists an $(n,R+\delta,\varepsilon)$ source code for all $\varepsilon\in(0,1)$, $\delta>0$ and sufficiently large $n$.
--
--   The direct coding theorem: the rate
--
--   $$
--   R=H(X)
--   $$
--
--   is achievable for $X$.
--
--   This is the half $\inf\{R: R\text{ achievable}\}\le H(X)$ of Shannon's compression theorem (Theorem 14.4.1).
--
--   **Formalization Note** Achievability is the published `WildeQIT.IsAchievableSourceRate p R`: for every $\varepsilon\in(0,1)$ and $\delta>0$ there is $N$ such that for every $n\ge N$ there is a deterministic `SourceCode α n M` with $M\le 2^{n(R+\delta)}$ and error probability at most $\varepsilon$.
--
--   Differences from the source:
--   - reading: "the direct coding theorem is the direction LHS ≤ RHS — the proof exhibits a coding scheme with an achievable rate" → $H(X)$ itself is achievable; reason: the book's proof builds an $(n,H(X)+\delta,\varepsilon)$ code for every $\varepsilon,\delta$ and large $n$, which is exactly this; it is equivalent to LHS ≤ RHS, since achievable rates are upward closed and a rate $H(X)+\delta/2$ code with slack $\delta/2$ meets the $\delta$-condition for $H(X)$
--   - encoding: encoder into $\{0,1\}^{nR}$, a set of size $2^{nR}$ → encoder into `Fin M` with $M\le 2^{nR}$; reason: $nR$ need not be an integer; since $\delta>0$ is arbitrary and $\lceil\log_2 M\rceil\le n(R+\delta)$ for large $n$, both conventions give the same achievable rates
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §14.4, Theorem 14.4.1 and its direct coding theorem, pp. 429–431, eqs. (14.28)–(14.30)

import Definitions.Def_WildeQIT_sourceCode
import Definitions.Def_WildeQIT_entropy

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 14.4.1, direct
coding theorem, p. 430.
-/

namespace WildeQIT.Compression

/-- **Theorem 14.4.1, direct coding theorem** (Wilde, arXiv:1106.1445v8, pp. 430–431).
The entropy `H(X)` is an achievable compression rate for the i.i.d. source `X`: for every
`ε ∈ (0, 1)`, `δ > 0` and all sufficiently large `n` there is an `(n, H(X) + δ, ε)` source code.

Formalization Note: the source `X` is a distribution `p` on a finite alphabet `α`, entropy in
bits. An `(n, R, ε)` source code is `WildeQIT.SourceCode α n M` with `M ≤ 2^{nR}` codewords and
error probability `Pr{D(E(Xⁿ)) ≠ Xⁿ} ≤ ε` (`WildeQIT.IsAchievableSourceRate`). -/
theorem theorem_14_4_1_direct {α : Type} [Fintype α] [DecidableEq α] (p : FinDist α) :
    IsAchievableSourceRate p (entropy p) := by sorry

end WildeQIT.Compression
