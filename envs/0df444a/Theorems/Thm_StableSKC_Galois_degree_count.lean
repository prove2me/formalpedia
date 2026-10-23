-- Prove2me | Theorems.Thm_StableSKC_Galois_degree_count
-- name    : StableSKC.Galois.degree_count
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:26.558831+00:00
-- url     : https://prove2.me/theorems/0113de9f-622b-436a-a627-4e130bf56ec7
-- title:
--   Proof of Theorem 3.1, p. 11 — #{r ∈ GF(2^k) : r ≠ 0, 1 + d(r) = i} = 2^{i−1}
-- statement:
--   Let $\mathrm{GF}(2^k)$ be presented with a root $\alpha$ of an irreducible polynomial of degree $k$ over $\mathbb Z_2$, and let $d(r) = \max\{j : r_j \ne 0\}$ be the degree of $r = \sum_{j=0}^{k-1} r_j \alpha^j$. Then for every round $i = 1, \dots, k$,
--   $$\#\{r \in \mathrm{GF}(2^k) : r \ne 0,\ 1 + d(r) = i\} = 2^{i-1}.$$
--
--   This is the counting step of the proof of Theorem 3.1: the number of tournaments $T(z)$ in which two given distinct players can meet in round $i$ equals the number of nonzero field elements of degree $i - 1$.
--
--   **Formalization Note** The proof of Theorem 3.1 on p. 11 prints the value as $2^i$. That is a misprint: the elements of degree exactly $i-1$ are those with $r_{i-1} = 1$, $r_j = 0$ for $j \ge i$ and $r_0, \dots, r_{i-2}$ arbitrary, which gives $2^{i-1}$, in agreement with the stability count $c_i = 2^{i-1}$ stated on p. 4. The formal statement uses $2^{i-1}$.
-- source:
--   Lambers, Pendavingh & Spieksma, How to Design a Stable Serial Knockout Competition, arXiv:2211.02513v1, p. 11, proof of Theorem 3.1 (printed as 2^i; corrected to 2^{i−1}, cf. p. 4)

import Mathlib
import Definitions.Def_StableSKC_Galois_Model

namespace StableSKC.Galois
theorem degree_count {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
    (pb : PowerBasis (ZMod 2) F) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ pb.dim) :
    (Finset.univ.filter fun r : F => r ≠ 0 ∧ 1 + deg pb r = i).card = 2 ^ (i - 1) := by sorry
end StableSKC.Galois
