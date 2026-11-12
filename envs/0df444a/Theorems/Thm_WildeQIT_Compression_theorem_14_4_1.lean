-- Prove2me | Theorems.Thm_WildeQIT_Compression_theorem_14_4_1
-- name    : WildeQIT.Compression.theorem_14_4_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T17:20:31.154419+00:00
-- url     : https://prove2.me/theorems/a3792b11-a818-47d3-9e89-dc8bbd52d0aa
-- title:
--   Theorem 14.4.1 (Shannon Compression): $\inf\{R: R\text{ achievable for }X\}=H(X)$
-- statement:
--   Let $X$ be a discrete random variable with distribution $p_X$ on a finite alphabet $\mathcal X$ and entropy $H(X)=-\sum_xp_X(x)\log p_X(x)$ in bits, and consider the i.i.d. information source $X^n=X_1\cdots X_n$. An $(n,R,\varepsilon)$ source code consists of a deterministic encoder $\mathcal E$ from $\mathcal X^n$ into a set of at most $2^{nR}$ codewords and a deterministic decoder $\mathcal D$ back to $\mathcal X^n$, with error probability
--
--   $$
--   p(e)=\Pr\{(\mathcal D\circ\mathcal E)(X^n)\neq X^n\}\le\varepsilon .
--   $$
--
--   A compression rate $R$ is achievable for $X$ if there exists an $(n,R+\delta,\varepsilon)$ source code for all $\varepsilon\in(0,1)$, $\delta>0$ and sufficiently large $n$.
--
--   **Theorem (Shannon compression).** The entropy is the smallest achievable rate for compression:
--
--   $$
--   \inf\{R: R\text{ is achievable for }X\}=H(X).
--   $$
--
--   This gives the entropy its operational meaning as the number of bits per source symbol needed to describe an i.i.d. source with vanishing error, and it is the classical special case of Schumacher compression.
--
--   **Formalization Note** Achievability is the published `WildeQIT.IsAchievableSourceRate p R`, and the infimum is Mathlib's real `sInf`. The set of achievable rates is nonempty ($\log_2|\mathcal X|$ is achievable by the identity code) and bounded below by $0$, so `sInf` is the true infimum; both facts are proved in a sanity file.
--
--   Differences from the source:
--   - encoding: $\inf$ of a set of reals → Mathlib's `sInf`; reason: the set is nonempty and bounded below (proved), so the value is the book's infimum
--   - encoding: encoder into $\{0,1\}^{nR}$, a set of size $2^{nR}$ → encoder into `Fin M` with $M\le 2^{nR}$; reason: $nR$ need not be an integer; since $\delta>0$ is arbitrary and $\lceil\log_2 M\rceil\le n(R+\delta)$ for large $n$, both conventions give the same achievable rates
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §14.4, Theorem 14.4.1, p. 430, eq. (14.30); definitions (14.28)–(14.29), pp. 429–430

import Definitions.Def_WildeQIT_sourceCode
import Definitions.Def_WildeQIT_entropy

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 14.4.1, p. 430.
-/

namespace WildeQIT.Compression

/-- **Theorem 14.4.1 (Shannon Compression)** (Wilde, arXiv:1106.1445v8, p. 430, eq. (14.30)).
The entropy of an information source specified by a discrete random variable `X` is the
smallest achievable rate for compression: `inf {R : R is achievable for X} = H(X)`.

Formalization Note: the source `X` is a distribution `p` on a finite alphabet `α`, entropy in
bits; achievability is `WildeQIT.IsAchievableSourceRate`. The infimum is Mathlib's real `sInf`;
the set of achievable rates is nonempty (`log₂ |α|` is achievable by the identity code) and
bounded below by `0` (a code with fewer than one codeword does not exist), so `sInf` is the true
infimum and not a junk value (checked in
`Solutions/verification/WildeQIT_Compression_sanity.lean`). -/
theorem theorem_14_4_1 {α : Type} [Fintype α] [DecidableEq α] (p : FinDist α) :
    sInf {R : ℝ | IsAchievableSourceRate p R} = entropy p := by sorry

end WildeQIT.Compression
