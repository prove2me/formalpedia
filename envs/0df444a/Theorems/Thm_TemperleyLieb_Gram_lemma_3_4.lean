-- Prove2me | Theorems.Thm_TemperleyLieb_Gram_lemma_3_4
-- name    : TemperleyLieb.Gram.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:44:37.462999+00:00
-- url     : https://prove2.me/theorems/5746f8f4-6bd3-4280-a8ba-1511c45dc8cf
-- title:
--   Lemma 3.4, p. 13 — sum identities for the polynomials p_i (with (3.3) as proved)
-- statement:
--   Let $p_i\in\mathbb Z[x]$ be defined by $p_0=0$, $p_1=1$ and $p_{i+1}=xp_i-p_{i-1}$. For integers $0\le j\le i$:
--
--   $$p_{2j}+p_{2j+2}+\cdots+p_{2i}=p_{i-k+1}p_{i+k}-p_{j-k}p_{j+k-1},\qquad k\in\{1,\dots,j\},\tag{3.3}$$
--
--   $$p_{2j+1}+p_{2j+3}+\cdots+p_{2i+1}=p_{i-k+1}p_{i+k+1}-p_{j-k}p_{j+k},\qquad k\in\{0,\dots,j\}.\tag{3.4}$$
--
--   These identities evaluate the sums of $p$'s that arise when the central elements $z_i$ act on the generator of a cell module (Lemma 3.5).
--
--   **Formalization Note** The page prints the last factor of (3.3) as $p_{j+k+1}$; that version is false: at $i=j=2$, $k=1$ the left side is $p_4=x^3-2x$ and the printed right side is $p_2p_3-p_1p_4=x$. The telescoping sum in the proof on p. 14 yields $p_{j+k-1}$, which is the form stated here. The range $j\le i$ is implicit in the notation $p_{2j}+\cdots+p_{2i}$.
-- source:
--   Enyang, Representations of Temperley–Lieb Algebras, arXiv:0710.3218v1, p. 13, Lemma 3.4, Eqs. (3.3)–(3.4); p. 14, proof (telescoping sum); p. 13, definition of p_i

import Mathlib
import Definitions.Def_TemperleyLieb_Gram_JM

namespace TemperleyLieb.Gram
open scoped BigOperators

/-- Enyang, Lemma 3.4, p. 13. Identity (3.3) is stated in the form its proof on
p. 14 derives (last factor `p_{j+k-1}`); the printed `p_{j+k+1}` is false
(`i = j = 2`, `k = 1`). Identity (3.4) is as printed. Both sums run over
`j ≤ m ≤ i`. -/
theorem lemma_3_4 :
    (∀ i j k : ℕ, j ≤ i → 1 ≤ k → k ≤ j →
      ∑ m ∈ Finset.Icc j i, p (2 * m) =
        p (i - k + 1) * p (i + k) - p (j - k) * p (j + k - 1)) ∧
    (∀ i j k : ℕ, j ≤ i → k ≤ j →
      ∑ m ∈ Finset.Icc j i, p (2 * m + 1) =
        p (i - k + 1) * p (i + k + 1) - p (j - k) * p (j + k)) := by sorry

end TemperleyLieb.Gram
