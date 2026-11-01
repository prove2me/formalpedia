-- Prove2me | Theorems.Thm_WildeQIT_Compression_theorem_14_4_1_converse
-- name    : WildeQIT.Compression.theorem_14_4_1_converse
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:30.56298+00:00
-- url     : https://prove2.me/theorems/d0d5f13f-840a-4b78-8088-628d01ff3608
-- title:
--   Theorem 14.4.1, converse theorem: every achievable compression rate is at least $H(X)$
-- statement:
--   Let $X$ be a discrete random variable with distribution $p_X$ on a finite alphabet $\mathcal X$ and entropy $H(X)$ in bits. A rate $R$ is achievable for $X$ if there exists an $(n,R+\delta,\varepsilon)$ source code (an encoder into at most $2^{n(R+\delta)}$ codewords and a decoder, with error probability $\Pr\{(\mathcal D\circ\mathcal E)(X^n)\neq X^n\}\le\varepsilon$) for all $\varepsilon\in(0,1)$, $\delta>0$ and sufficiently large $n$.
--
--   The converse theorem: every achievable rate $R$ for $X$ satisfies
--
--   $$
--   R\ge H(X) .
--   $$
--
--   Equivalently, no coding scheme with rate below the entropy is achievable; this is the half $\inf\{R: R\text{ achievable}\}\ge H(X)$ of Shannon's compression theorem (Theorem 14.4.1). The book proves it later, as a special case of the converse of Schumacher compression (Chapter 18).
--
--   **Formalization Note** Achievability is the published `WildeQIT.IsAchievableSourceRate p R` with deterministic encoder and decoder.
--
--   Differences from the source:
--   - encoding: encoder into $\{0,1\}^{nR}$, a set of size $2^{nR}$ → encoder into `Fin M` with $M\le 2^{nR}$; reason: $nR$ need not be an integer; since $\delta>0$ is arbitrary, both conventions give the same achievable rates
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §14.4, Theorem 14.4.1 and its converse theorem, pp. 430–431, eqs. (14.28)–(14.30)

import Definitions.Def_WildeQIT_sourceCode
import Definitions.Def_WildeQIT_entropy

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 14.4.1, converse
theorem, p. 430.
-/

namespace WildeQIT.Compression

/-- **Theorem 14.4.1, converse theorem** (Wilde, arXiv:1106.1445v8, pp. 430–431).
No rate below the entropy is achievable: every achievable compression rate `R` for the i.i.d.
source `X` satisfies `R ≥ H(X)`.

Formalization Note: the source `X` is a distribution `p` on a finite alphabet `α`, entropy in
bits; achievability is `WildeQIT.IsAchievableSourceRate` (§14.4: an `(n, R + δ, ε)` source code
for all `ε ∈ (0, 1)`, `δ > 0` and sufficiently large `n`). -/
theorem theorem_14_4_1_converse {α : Type} [Fintype α] [DecidableEq α] (p : FinDist α)
    (R : ℝ) (hR : IsAchievableSourceRate p R) : entropy p ≤ R := by sorry

end WildeQIT.Compression
