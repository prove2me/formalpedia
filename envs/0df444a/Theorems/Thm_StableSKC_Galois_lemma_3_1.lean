-- Prove2me | Theorems.Thm_StableSKC_Galois_lemma_3_1
-- name    : StableSKC.Galois.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:22.711269+00:00
-- url     : https://prove2.me/theorems/188e5bb8-72e7-478e-ae4c-1438fa51f318
-- title:
--   Lemma 3.1, p. 10 — a knockout tournament T on GF(2^k) with v_T(x, y) = 1 + d(x − y)
-- statement:
--   Let $\mathrm{GF}(2^k)$ be presented as $\mathbb Z_2[X]/(q)$ for an irreducible $q$ of degree $k$ with root $\alpha$, and let $d(x) = \max\{i : x_i \ne 0\}$ be the degree of $x = \sum_{i=0}^{k-1} x_i\alpha^i$. Then there is a knockout tournament $T$ whose $2^k$ players are the elements of $\mathrm{GF}(2^k)$ such that, for all distinct $x, y \in \mathrm{GF}(2^k)$,
--   $$v_T(x, y) = 1 + d(x - y),$$
--   that is, $x$ and $y$ can meet in round $1 + d(x-y)$ of $T$.
--
--   In such a tournament the round in which two players can meet depends only on their difference. This is the starting point of the construction: relabelling $T$ by the nonzero field elements produces a stable serial knockout competition (Theorem 3.1). In particular, the lemma shows that the hypothesis of the formalized Theorem 3.1 is satisfiable for every $k$.
--
--   **Formalization Note** The field is a type `F` with a power basis `pb` over `ZMod 2` of dimension $k$ = `pb.dim`; the tournament is a seeding `Seeding pb.dim F`. The identity is required only for $x \ne y$, since the page leaves $d(0)$, and hence $v_T(x, x)$, undefined.
-- source:
--   Lambers, Pendavingh & Spieksma, How to Design a Stable Serial Knockout Competition, arXiv:2211.02513v1, p. 10, Lemma 3.1

import Mathlib
import Definitions.Def_StableSKC_Galois_Model

namespace StableSKC.Galois
theorem lemma_3_1 {F : Type*} [Field F] [Algebra (ZMod 2) F] (pb : PowerBasis (ZMod 2) F) :
    ∃ T : Seeding pb.dim F, ∀ x y : F, x ≠ y → CanMeetIn T x y (1 + deg pb (x - y)) := by sorry
end StableSKC.Galois
