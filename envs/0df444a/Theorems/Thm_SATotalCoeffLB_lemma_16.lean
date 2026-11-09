-- Prove2me | Theorems.Thm_SATotalCoeffLB_lemma_16
-- name    : SATotalCoeffLB.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:20:57.142494+00:00
-- url     : https://prove2.me/theorems/91b26eb1-98b7-4e6a-a659-167ebcf66625
-- title:
--   Lemma 16 — nonzero codeword forms have rank $\ge \delta n/16$
-- statement:
--   Let $E \subseteq \binom{[n]}{2}$ be a set of $m = |E|$ pairs (a graph on $[n]$) of maximum degree at most $8$ with $m \ge 2n$, let $\delta > 0$, and let $C \subseteq \mathbb F_2^E$ be a linear code in which every nonzero codeword has Hamming weight at least $\delta m$. Then for every nonzero $z \in C$,
--
--   $$
--   \operatorname{rank}(a_z) \ge \frac{\delta n}{16},
--   $$
--
--   where $a_z(\bar x) = \sum_{e=\{i,j\}\in E} z_e \bar x_i \bar x_j$ and $\operatorname{rank}$ is the $\mathbb F_2$-rank of the polar matrix (Definition 3). In the paper's words: every nonzero $a \in L = \{a_z : z \in C\}$ has rank at least $\delta n/16$.
--
--   This is the rank property on which the functional $L_0$ of Lemma 17 rests: two forms of rank at most $\tau n$ cannot differ by a nonzero element of $L$.
--
--   Differences from the source:
--   - generalization: for all sufficiently large $m$, with $n = \lceil m/4\rceil$, $E$ the degree-8 graph of Section 9.1 and $C$ the code of Lemma 15 → any $E$ of maximum degree $\le 8$ with $|E| \ge 2n$ and any linear $C \subseteq \mathbb F_2^E$ of minimum distance $\ge \delta|E|$; reason: the page's proof uses only these three facts ($m \ge 2n$ is its last step); $n = \lceil m/4\rceil$ gives $m \ge 2n$ for every $m \ge 2$
--   - encoding: nonzero $a \in L$ → $a_z$ with $z \in C$, $z \ne 0$; reason: $z \mapsto a_z$ is injective, so $a_z \ne 0$ iff $z \ne 0$
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Lemma 16, p.51 (with Definition 3 and the definition of a_z and L, p.51)

import Mathlib
import Definitions.Def_SATotalCoeffLB_qrank
import Definitions.Def_SATotalCoeffLB_formOf

namespace SATotalCoeffLB

/-- **Lemma 16 (codeword forms have high rank)**, p.51 of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178).

Let `E` be a set of `m` pairs on `[n]` (a graph without loops or repeated edges) of maximum degree
at most eight with `m ≥ 2n`, and let `C ⊆ F₂^E` be a linear code of minimum distance at least
`δm`, `δ > 0`. Then every nonzero form `a_z`, `z ∈ C`, of `L = {a_z : z ∈ C}` has
`rank(a_z) ≥ δn/16`.

**Formalization Note** The page's "for all sufficiently large `m`" (with `n = ⌈m/4⌉`) is used in
the proof only through `m ≥ 2n`; the lemma is stated under that hypothesis, the degree bound and
the distance bound. `a_z ≠ 0` iff `z ≠ 0`. -/
theorem lemma_16 (n : ℕ) (E : Finset (Pair n))
    (hdeg : ∀ v : Fin n, (E.filter fun e => e.1.1 = v ∨ e.1.2 = v).card ≤ 8) (hm : 2 * n ≤ E.card)
    (δ : ℝ) (hδ : 0 < δ) (C : Submodule (ZMod 2) (E → ZMod 2))
    (hdist : ∀ z ∈ C, z ≠ 0 → δ * E.card ≤ (hammingNorm z : ℝ)) :
    ∀ z ∈ C, z ≠ 0 → δ * n / 16 ≤ (qrank (formOf E z) : ℝ) := by sorry

end SATotalCoeffLB
